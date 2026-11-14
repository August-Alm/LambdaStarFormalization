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

def DefEnv.empty : DefEnv where
  defs _ := none
  closed _ _ defined := by cases defined

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
bodies become generally operational after validation.
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
