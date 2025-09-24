------------------------------------------ Proc  ------------------------------------------

abbrev Name := String

structure NonEmptyName where
  (val : String)
  (ne_empty : val ≠ " ")
deriving Repr, BEq, DecidableEq

inductive Proc where
  | send : NonEmptyName → Name → Proc → Proc      -- x[y].P ∧ x[].P (output y on x and continue as P)
  | receive : NonEmptyName → Name → Proc → Proc   -- x(y).P ∧ x().P (input y on x and continue as P)
  | cut : NonEmptyName → NonEmptyName → Proc      -- vxy P          (name restriction, or "cut")
  | par : Proc → Proc → Proc                      -- parallel composition of two processes
  | nil : Proc                                    -- terminated process
deriving Repr

notation:60 x "[" y "]" "." P => Proc.send x y P
notation:60 x "(" y ")" "." P => Proc.receive x y P
notation:60 "v" x y P => Proc.cut x y P
infixr:55 " ∣ " => Proc.par                         -- normal pipe creates issues with lean's matching so this is \mid
notation "𝟘" => Proc.nil

------------------------------------------ TYPES  ------------------------------------------

-- def NonEmptyTypes := { s : String // s ≠ "" ∧ s.all Char.isUpper ∨ s = "∅" }

-- instance : Repr NonEmptyTypes where
--   reprPrec  s _ := "NonEmptyTypes(\"" ++ s.val ++ "\")"

structure NonEmptyTypes where
  (val : String)
  (restriction : val ≠ " " ∧ val.all Char.isUpper ∨ val = "∅")
deriving Repr, BEq, DecidableEq

inductive Types where
  | term : NonEmptyTypes → Types        -- named type, like A, B, ...
  | send : Types → Types → Types        -- send arg₁ continue as arg₂
  | receive : Types → Types → Types     -- receive arg₁ continue as arg₂
  | one : Types                         -- 1 (empty output, unit for ⊗)
  | bot : Types                         -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

notation:60 A " ⊗ " B => Types.send A B
notation:60 A " ⅋ " B => Types.receive A B
notation "𝟙" => Types.one
notation "⊥" => Types.bot

--------------------------------------- ENVIRONMENTS ---------------------------------------

def upperCaseGreekLetters : List (Char) :=
  ['Α', 'Β', 'Γ', 'Δ', 'Ε', 'Ζ', 'Η', 'Θ', 'Ι', 'Κ', 'Λ', 'Μ',
  'Ν', 'Ξ', 'Ο', 'Π', 'Ρ', 'Σ', 'Τ', 'Υ', 'Φ', 'Χ', 'Ψ', 'Ω']

structure EnvNames where
  (val : { s : String // s ≠ " " ∧ s.all (· ∈ upperCaseGreekLetters) })
deriving Repr, BEq, DecidableEq

-- structure Env where
  -- (name : EnvNames) -- Currently restricted to uppercase greek letters
--   (data : List (NonEmptyName × Types))
-- deriving Repr

abbrev Env := List (NonEmptyName × Types)
abbrev EmptyEnv : Env := []

-- Prop stating that all process names in an environment must be distinct
-- def envLinearity (Δ : Env) : Prop :=
--   ∀ x : NonEmptyName,
--     (Δ.data.filter (fun p => p.fst == x)).length ≤ 1

-- def envLookupTypeOf (Δ : Env) (x : NonEmptyName) : Option Types :=
--   ((Δ.data.find? (fun p => p.fst == x)).map) Prod.snd

def envLookupTypeOf (Δ : Env) (x : NonEmptyName) : Option Types :=
  ((Δ.find? (fun p => p.fst == x)).map) Prod.snd








------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

-- def calligraphyLetters : List (Char) :=
--   ['𝒜', 'ℬ', '𝒞', '𝒟', 'ℰ', 'ℱ', '𝒢', 'ℋ', 'ℐ', '𝒥', '𝒦', 'ℒ', 'ℳ',
--   '𝒩', '𝒪', '𝒫', '𝒬', 'ℛ', '𝒮', '𝒯', '𝒰', '𝒱', '𝒲', '𝒳', '𝒴', '𝒵']

-- structure HyperNames where
--   (val : { s : String // s ≠ "" ∧ s.all (· ∈ calligraphyLetters) ∨ s = "∅" })
-- deriving Repr, BEq, DecidableEq

-- instance : Repr HyperNames where
--   reprPrec he _ := "HyperName(\"" ++ he.val.val ++ "\")"

-- structure HyperEnv where
--   (name : HyperNames) -- Currently restricted to calligraphy letters
--   (data : List (Env))
-- deriving Repr

structure HyperEnv where
  (data : List (EnvNames × Env))
deriving Repr, BEq, DecidableEq

abbrev EmptyHyperEnv : HyperEnv := { data := [] }

-- Prop stating all environment names in a hyper-environment must be distinct
-- def hyperLinearity (𝒢 : HyperEnv) : Prop :=
--   ∀ x : EnvNames,
--     (𝒢.data.filter (fun p => p.name == x)).length ≤ 1

-- def hyperLookupTypeOf (𝒢 : HyperEnv) (x : NonEmptyName) : Option Types :=
--   (𝒢.data.find? (fun Δ =>
--     (Option.isSome (envLookupTypeOf Δ x)))).bind (fun Δ => envLookupTypeOf Δ x)

def hyperLookupTypeOf (𝒢 : HyperEnv) (x : NonEmptyName) : Option Types :=
  (𝒢.data.findSome? (fun Δ => envLookupTypeOf Δ.snd x))

  notation 𝒢 "(" x ")" => hyperLookupTypeOf 𝒢 x












------------------------------------------ TODOs  ------------------------------------------

-- TODO: Define partial commutative monoid with ',' acting as sum and • acting as unit
--  Γ,• = Γ     Γ,Δ = Δ,Γ       (Γ,Δ),Ξ = Γ,(Δ,Ξ)
-- probably shouldn't be the actual ',' symbol but something close

-- TODO: Define partial commutative monoid with '|ₕ' acting as sum and ∅ as unit
-- G|∅ = G      G|H = H|G     (G|H)|I = G|(H|I)

-- TODO: Define dual operator s.t:
  -- (𝐴 ⊗ 𝐵)^⊥ = 𝐴^⊥ ⅋ 𝐵^⊥
  -- (𝐴 ⅋ 𝐵)^⊥ = 𝐴^⊥ ⊗ 𝐵^⊥
  -- 1^⊥ = ⊥
  -- ⊥^⊥ = 1

-- make notation for:
  -- combininig environments using the comma operator, having bigdot as unit
  -- combining hyper-environment using another parallel, having ∅ as unit
  -- creating a hyper-environment when doing parallel composition of multiple environments

-- TODO: make environments and hyper-environments ignore the order of their elements

-- TODO: Define name function returning the names in a hyper-/environment
-- TODO: define typing rules with side condition enforcing
  -- Environments can only contain one occurence of a process name
  -- Hyper-environments can only contain one occurence of an environment name



-- TODO: define wellformedness for hyper-environments

-- TODO: make a smart constructor for hyper-environments for less boiler plate?


------------ Might be irrelevant ------------
-- TODO: use env_linearity to ensure insertions / appends to an env's data are unique entries
-- TODO: use hyper_linearity to ensure insertions / appends to an hyperenv's data are unique entries
