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
An implementation realizes its declared type. Ordinary definitions check the
body directly. For a previously validated named self type `A = ιx.T`, the
implementation of `c : A` checks against `T[c/x]`, preserving `c` as the self
index instead of substituting the implementation body for it. Type formation
uses `formationContext`; every value-producing case uses `realizationContext`.
-/
inductive ChecksImplementation
    (prior : DefEnv) (formationContext realizationContext : TypingContext)
    (name : Const) (body : Term) : Term → Prop where
  | typeFormation (check : Checks prior formationContext body .star) :
      ChecksImplementation prior formationContext realizationContext
        name body .star
  | direct (check : Checks prior realizationContext body type) :
      ChecksImplementation prior formationContext realizationContext
        name body type
  | namedSelf
      (defined : prior.defs typeName = some (.iota selfBody))
      (check : Checks prior realizationContext body
        (selfBody.instantiate (.const name))) :
      ChecksImplementation prior formationContext realizationContext
        name body (.const typeName)
  | namedSelfFunction
      (bodyShape : body = .lam functionBody)
      (defined : prior.defs typeName = some (.iota selfBody))
      (check : Checks prior (realizationContext.bind domain) functionBody
        (selfBody.instantiate
          (.app (.const name)
            (.app (domain.shift 1 0) (.bvar 0))))) :
          ChecksImplementation prior formationContext realizationContext name body
        (Term.arrow domain (.const typeName))

/--
An accepted implementation supplies the appropriate projector equality. The
named-self case records the validated type body and keeps the closure name as
the self index.
-/
theorem ChecksImplementation.sound
    (implementation : ChecksImplementation prior formationContext
      realizationContext name body type) :
    (type = .star ∧
      ContextEquiv prior formationContext (.app .star body) body) ∨
    ContextEquiv prior realizationContext (.app type body) body ∨
      (∃ typeName selfBody,
        type = .const typeName ∧
        prior.defs typeName = some (.iota selfBody) ∧
        ContextEquiv prior realizationContext
          (.app (selfBody.instantiate (.const name)) body) body) ∨
      (∃ domain typeName selfBody functionBody,
        body = .lam functionBody ∧
        type = Term.arrow domain (.const typeName) ∧
        prior.defs typeName = some (.iota selfBody) ∧
        ContextEquiv prior (realizationContext.bind domain)
          (.app
            (selfBody.instantiate
              (.app (.const name)
                (.app (domain.shift 1 0) (.bvar 0))))
            functionBody)
          functionBody) := by
  cases implementation with
  | typeFormation check => exact Or.inl ⟨rfl, check.sound⟩
  | direct check => exact Or.inr (Or.inl check.sound)
  | @namedSelf typeName selfBody defined check =>
      exact Or.inr (Or.inr
        (Or.inl ⟨typeName, selfBody, rfl, defined, check.sound⟩))
  | namedSelfFunction bodyShape defined check =>
      exact Or.inr (Or.inr (Or.inr
        ⟨_, _, _, _,
          bodyShape, rfl, defined, check.sound⟩))

/--
One validation phase. All signatures are available for type formation. Value
realization excludes every signature implemented in this phase, preventing
self-certification and same-phase mutual certification. Reduction may unfold
only `prior`; phase bodies become operational after validation.
-/
structure ChecksRecursivePhase
    (prior : DefEnv) (signatures : List RecursiveSignature)
    (bodies : List RecursiveBody) : Prop where
  signaturesUnique : (signatures.map (·.name)).Nodup
  namesUnique : (bodies.map (·.name)).Nodup
  fresh : ∀ definition ∈ bodies, prior.defs definition.name = none
  declared : ∀ definition ∈ bodies,
    ∃ type, RecursiveSignature.lookup signatures definition.name = some type ∧
      ChecksImplementation prior (RecursiveSignature.context signatures)
        (RecursiveSignature.contextWithout signatures (bodies.map (·.name)))
        definition.name definition.body type

/-- A sequence of phases, each exposing only previously validated bodies. -/
inductive ChecksRecursiveBlock
    (signatures : List RecursiveSignature) :
    DefEnv → List (List RecursiveBody) → DefEnv → Prop where
  | nil : ChecksRecursiveBlock signatures environment [] environment
  | cons
      (phase : ChecksRecursivePhase prior signatures bodies)
      (rest : ChecksRecursiveBlock signatures (prior.extend bodies) phases result) :
      ChecksRecursiveBlock signatures prior (bodies :: phases) result

/-- A validated declaration has its signature without unfolding its own body. -/
theorem ChecksRecursivePhase.hasType
    (phase : ChecksRecursivePhase prior signatures bodies)
    (membership : definition ∈ bodies) :
    ∃ type, RecursiveSignature.lookup signatures definition.name = some type ∧
      ChecksImplementation prior (RecursiveSignature.context signatures)
        (RecursiveSignature.contextWithout signatures (bodies.map (·.name)))
        definition.name definition.body type :=
  phase.declared definition membership

end LambdaStar
