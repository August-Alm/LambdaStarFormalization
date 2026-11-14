import LambdaStar.SelfTyping

namespace LambdaStar

/-- A recursive name and its declared operational type. -/
structure RecursiveSignature where
  name : Const
  type : Term
  typeClosed : type.Closed

/-- A closed body proposed for one recursive name. -/
structure RecursiveBody where
  name : Const
  body : Term
  bodyClosed : body.Closed

namespace RecursiveSignature

/-- All recursive signatures, used while checking type formation. -/
def context (signatures : List RecursiveSignature) : TypingContext :=
  signatures.map fun signature =>
    (.app signature.type (.const signature.name), .const signature.name)

/-- Signature equations excluding names implemented in the current phase. -/
def contextWithout (signatures : List RecursiveSignature)
    (excluded : List Const) : TypingContext :=
  match signatures with
  | [] => []
  | signature :: signatures =>
      if signature.name ∈ excluded then contextWithout signatures excluded
      else
        (.app signature.type (.const signature.name), .const signature.name) ::
          contextWithout signatures excluded

def lookup (signatures : List RecursiveSignature) (name : Const) : Option Term :=
  match signatures with
  | [] => none
  | signature :: signatures =>
      if signature.name = name then some signature.type
      else lookup signatures name

end RecursiveSignature

namespace RecursiveBody

def lookup (bodies : List RecursiveBody) (name : Const) : Option Term :=
  match bodies with
  | [] => none
  | definition :: bodies =>
      if definition.name = name then some definition.body
      else lookup bodies name

theorem closed_of_lookup
    {name : Const} {term : Term}
    (defined : lookup bodies name = some term) : term.Closed := by
  induction bodies with
  | nil => simp [lookup] at defined
  | cons definition bodies inductionHypothesis =>
      by_cases hMatches : definition.name = name
      · simp [lookup, hMatches] at defined
        cases defined
        exact definition.bodyClosed
      · simp [lookup, hMatches] at defined
        exact inductionHypothesis defined

end RecursiveBody

/-- Extend an environment only with bodies validated in one completed phase. -/
def DefEnv.extend (prior : DefEnv) (bodies : List RecursiveBody) : DefEnv where
  defs name := (RecursiveBody.lookup bodies name).orElse fun _ => prior.defs name
  closed name body defined := by
    unfold Option.orElse at defined
    split at defined
    next phaseBody equality =>
      cases defined
      exact RecursiveBody.closed_of_lookup equality
    next missing =>
      exact prior.closed name body defined

/--
An implementation realizes its declared type. Recursive type formation checks
the closure name in a provisional environment containing the phase bodies;
ordinary and value-producing cases unfold only the prior environment. Every
case uses a context with current-phase signatures removed. For a previously
validated named self-indexed projector, the implementation of `k : c` checks
against `T[k/x]`, preserving `k` as the index instead of substituting its body.
-/
inductive ChecksImplementation
    (prior formation : DefEnv) (context : TypingContext)
    (name : Const) : Term → Term → Prop where
  | typeFormation (check : Checks prior prior context body .star) :
      ChecksImplementation prior formation context
        name body .star
  | recursiveTypeFormation
      (defined : formation.defs name = some body)
      (check : Checks prior formation context (.const name) .star) :
      ChecksImplementation prior formation context name body .star
  | direct (check : Checks prior prior context body type) :
      ChecksImplementation prior formation context
        name body type
  | namedSelf
      (defined : prior.defs typeName = some (Term.self selfBody))
      (check : Checks prior prior context body
        (selfBody.instantiate (.const name))) :
      ChecksImplementation prior formation context
        name body (.const typeName)
  | namedSelfFunction
      (defined : prior.defs typeName = some (Term.self selfBody))
      (check : Checks prior prior (context.bind domain) functionBody
        (selfBody.instantiate
          (.app (.const name)
            (.app (domain.shift 1 0) (.bvar 0))))) :
          ChecksImplementation prior formation context
            name (.lam functionBody)
        (Term.arrow domain (.const typeName))

/--
One validation phase. Checking excludes every signature implemented in this
phase, preventing direct signature-based self-certification. Recursive type
formation may unfold the provisional phase environment only through its
guarded idempotence proof; value-producing cases unfold only `prior`. Phase
bodies become locally available to later phases through index-consuming delta.
Only a complete signature-covered block can be sealed as a `ValidatedEnv`.
-/
structure ChecksRecursivePhase
    (prior : DefEnv) (signatures : List RecursiveSignature)
    (bodies : List RecursiveBody) : Prop where
  signaturesUnique : (signatures.map (·.name)).Nodup
  namesUnique : (bodies.map (·.name)).Nodup
  fresh : ∀ definition ∈ bodies, prior.defs definition.name = none
  declared : ∀ definition ∈ bodies,
    ∃ type, RecursiveSignature.lookup signatures definition.name = some type ∧
      ChecksImplementation prior
        (prior.extend bodies)
        (RecursiveSignature.contextWithout signatures (bodies.map (·.name)))
        definition.name definition.body type

/-- A sequence of phases, each exposing only previously validated bodies. -/
inductive ChecksRecursivePhases
    (signatures : List RecursiveSignature) :
    DefEnv → List (List RecursiveBody) → DefEnv → Prop where
  | nil : ChecksRecursivePhases signatures environment [] environment
  | cons
      (phase : ChecksRecursivePhase prior signatures bodies)
      (rest : ChecksRecursivePhases signatures (prior.extend bodies) phases result) :
      ChecksRecursivePhases signatures prior (bodies :: phases) result

/-- Names implemented across all phases of a recursive block. -/
def implementedNames (phases : List (List RecursiveBody)) : List Const :=
  phases.flatMap fun bodies => bodies.map (·.name)

/--
A complete recursive block validates its phases and implements every declared
signature. Phase declaration lookup already ensures that every body has a
signature; freshness prevents implementing one name in multiple phases.
-/
structure ChecksRecursiveBlock
    (signatures : List RecursiveSignature) (prior : DefEnv)
    (phases : List (List RecursiveBody)) (result : DefEnv) : Prop where
  validation : ChecksRecursivePhases signatures prior phases result
  signaturesCovered : ∀ signature ∈ signatures,
    signature.name ∈ implementedNames phases

/--
An environment is available at an observation depth only through validation
history. Depth zero observes no definitions, the empty environment is valid at
every depth, and each sealed complete block adds one observable layer.
-/
inductive EnvironmentSatisfiesAt : Nat → DefEnv → Prop where
  | zero (environment : DefEnv) : EnvironmentSatisfiesAt 0 environment
  | empty (depth : Nat) : EnvironmentSatisfiesAt depth DefEnv.empty
  | sealed
      (priorSatisfied : EnvironmentSatisfiesAt depth prior)
      (block : ChecksRecursiveBlock signatures prior phases result) :
      EnvironmentSatisfiesAt (depth + 1) result

/-- An environment backed by validation history at every finite depth. -/
def EnvironmentSatisfies (environment : DefEnv) : Prop :=
  ∀ depth, EnvironmentSatisfiesAt depth environment

namespace EnvironmentSatisfies

theorem empty : EnvironmentSatisfies DefEnv.empty := by
  intro depth
  exact .empty depth

/-- A complete checked block seals one new environment layer. -/
theorem sealBlock
    (priorSatisfied : EnvironmentSatisfies prior)
    (block : ChecksRecursiveBlock signatures prior phases result) :
    EnvironmentSatisfies result := by
  intro depth
  cases depth with
  | zero => exact .zero result
  | succ depth =>
      exact EnvironmentSatisfiesAt.sealed (priorSatisfied depth) block

end EnvironmentSatisfies

/-- A raw environment together with its complete block-validation history. -/
structure ValidatedEnv where
  raw : DefEnv
  satisfies : EnvironmentSatisfies raw

namespace ValidatedEnv

def empty : ValidatedEnv where
  raw := DefEnv.empty
  satisfies := EnvironmentSatisfies.empty

/-- Extend a validated environment only by sealing a complete checked block. -/
def sealBlock (prior : ValidatedEnv)
    (block : ChecksRecursiveBlock signatures prior.raw phases result) :
    ValidatedEnv where
  raw := result
  satisfies := EnvironmentSatisfies.sealBlock prior.satisfies block

end ValidatedEnv

/-
Ordinary finite evaluation is recovered at every base depth by supplying the
derivation's finite unfolding cost. In particular, delta consumes one depth;
there is deliberately no unrestricted same-world delta theorem.
-/
mutual
  theorem legacyStep_to_guarded
      (satisfied : EnvironmentSatisfies environment)
      (reduction : Step environment stage left right) :
      ∃ cost, ∀ baseDepth,
        GuardedStep environment environment (cost + baseDepth) baseDepth []
          left right :=
    match reduction with
    | .beta =>
        ⟨0, fun baseDepth => by
          simpa using
            (GuardedStep.legacy (prior := environment) (formation := environment)
              (depth := baseDepth)
              (Step.beta (Δ := DefEnv.empty) (stage := stage)))⟩
    | .delta defined =>
        ⟨1, fun baseDepth => by
          simpa [Nat.add_comm] using
            (GuardedStep.delta (formation := environment) (depth := baseDepth)
              defined)⟩
    | .starredIdempotence =>
        ⟨0, fun baseDepth => by
          simpa using
            (GuardedStep.legacy (prior := environment) (formation := environment)
              (depth := baseDepth)
              (Step.starredIdempotence (Δ := DefEnv.empty) (stage := stage)))⟩
    | .starChecking certificate => by
        obtain ⟨cost, translated⟩ :=
          legacySteps_to_guarded satisfied certificate
        exact ⟨cost, fun baseDepth => .starChecking (translated baseDepth)⟩
    | .lam reduction => by
        obtain ⟨cost, translated⟩ :=
          legacyStep_to_guarded satisfied reduction
        exact ⟨cost, fun baseDepth => .lam (translated baseDepth)⟩
    | .appLeft reduction => by
        obtain ⟨cost, translated⟩ :=
          legacyStep_to_guarded satisfied reduction
        exact ⟨cost, fun baseDepth => .appLeft (translated baseDepth)⟩
    | .appRight reduction => by
        obtain ⟨cost, translated⟩ :=
          legacyStep_to_guarded satisfied reduction
        exact ⟨cost, fun baseDepth => .appRight (translated baseDepth)⟩

  theorem legacySteps_to_guarded
      (satisfied : EnvironmentSatisfies environment)
      (reduction : Steps environment stage left right) :
      ∃ cost, ∀ baseDepth,
        GuardedSteps environment environment (cost + baseDepth) baseDepth []
          left right :=
    match reduction with
    | .refl => ⟨0, fun baseDepth => by simpa using GuardedSteps.refl⟩
    | .tail head tail => by
        obtain ⟨headCost, translatedHead⟩ :=
          legacyStep_to_guarded satisfied head
        obtain ⟨tailCost, translatedTail⟩ :=
          legacySteps_to_guarded satisfied tail
        exact ⟨headCost + tailCost, fun baseDepth => by
          simpa [Nat.add_assoc] using
            GuardedSteps.tail (translatedHead (tailCost + baseDepth))
              (translatedTail baseDepth)⟩
end

/-- Sealed finite evaluation has a guarded realization at every base depth. -/
theorem sealed_steps_sound (validated : ValidatedEnv)
    (reduction : Steps validated.raw stage left right) :
    ∃ cost, ∀ baseDepth,
      GuardedSteps validated.raw validated.raw (cost + baseDepth) baseDepth []
        left right :=
  legacySteps_to_guarded validated.satisfies reduction

/-- A uniformly costed guarded reduction is observable at every requested depth. -/
theorem costed_guarded_steps_equiv
    (reduction : ∃ cost, ∀ baseDepth,
      GuardedSteps environment environment (cost + baseDepth) baseDepth []
        left right) :
    ∀ depth, ContextEquiv environment environment depth [] left right := by
  obtain ⟨cost, reduction⟩ := reduction
  intro depth
  by_cases enough : cost ≤ depth
  · let baseDepth := depth - cost
    have sourceDepth : cost + baseDepth = depth := by
      simp [baseDepth, Nat.add_sub_of_le enough]
    apply ContextEquiv.operational
    refine ⟨baseDepth, right, ?_, ?_⟩
    · exact sourceDepth ▸ reduction baseDepth
    · exact sourceDepth ▸ GuardedSteps.spend cost baseDepth
  · apply ContextEquiv.operational
    refine ⟨0, right, ?_, GuardedSteps.spend depth 0⟩
    exact GuardedSteps.trans (GuardedSteps.spend depth 0)
      (GuardedSteps.single GuardedStep.zero)

/-- Every legacy reduction in a validated environment is equivalent at every depth. -/
theorem sealed_steps_equiv (validated : ValidatedEnv)
    (reduction : Steps validated.raw stage left right) :
    ∀ depth, ContextEquiv validated.raw validated.raw depth [] left right :=
  costed_guarded_steps_equiv (sealed_steps_sound validated reduction)

/-- A validated declaration has its signature without unfolding its own body. -/
theorem ChecksRecursivePhase.hasType
    (phase : ChecksRecursivePhase prior signatures bodies)
    (membership : definition ∈ bodies) :
    ∃ type, RecursiveSignature.lookup signatures definition.name = some type ∧
      ChecksImplementation prior
        (prior.extend bodies)
        (RecursiveSignature.contextWithout signatures (bodies.map (·.name)))
        definition.name definition.body type :=
  phase.declared definition membership

end LambdaStar
