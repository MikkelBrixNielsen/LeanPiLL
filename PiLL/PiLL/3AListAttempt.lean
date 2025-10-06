----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.List.AList
------------------------------------------ Proc  ------------------------------------------

abbrev PName := Nat -- Process names are just numbers (ensures not empty)

inductive Proc : Type where
  | tensor  (x y : PName) (P : Proc)   -- x[y].P
  | parr    (x y : PName) (P : Proc)   -- x(y).P
  | one     (x : PName) (P : Proc)     -- x[].P
  | bot     (x : PName) (P : Proc)     -- x().P
  | cut     (x y : PName) (P : Proc)   -- 𝒗xy P
  | par     (P Q : Proc)               -- P | Q
  | nil                                -- 𝟘
deriving Repr, BEq, DecidableEq

------------------------------------------ TYPES  ------------------------------------------
universe u

variable {Atom : Type u}

inductive Types (Atom : Type u) : Type u where
  | atom    (a : Atom)            -- A, B, ... (A typing term)
  | atomDual (a : Atom)           -- The dual of A, B ...
  | tensor  (A B : Types Atom)    -- t₁ ⊗ t₂ (send)
  | parr    (A B : Types Atom)    -- t₁ ⅋ t₂ (receive)
  | one                           -- 𝟙 (empty output, unit for ⊗)
  | bot                           -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

instance : Bot (Types Atom) := ⟨.bot⟩
instance : One (Types Atom) := ⟨.one⟩

-- TODO: define which Types are positive / negative
-- TODO: decidability for positive / negative propositions

def Types.pos : Types Atom → Prop
  | atom _ => True
  | one => True
  | tensor _ _ => True
  -- | oplus _ _ => True
  -- | bang _ => True
  -- | zero => True
  | _ => False

def Types.neg : Types Atom → Prop
  | atomDual _ => True
  | bot => True
  | parr _ _ => True
  -- | top => True
  -- | .with _ _ => True
  -- | quest _ => True
  | _ => False

instance Types.posDecidable (A : Types Atom) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negDecidable (A : Types Atom) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

@[simp]
def Types.dual : Types Atom → Types Atom
| .tensor A B => .parr (dual A) (dual B)
| .parr A B   => .tensor (dual A) (dual B)
| .one        => .bot
| .bot        => .one
| .atom a     => .atomDual a
| .atomDual a => .atom a

@[simp]
theorem Types.dual.neq (A : Types Atom) : A ≠ dual A := by
  cases A <;> simp [dual]

@[simp]
theorem dual.inj (A B : Types Atom) : Types.dual A = Types.dual B ↔ B = A := by
  induction A generalizing B <;> cases B
  all_goals aesop

@[simp]
theorem dual.involution (A : Types Atom) : Types.dual (Types.dual A) = A := by
  induction A <;> simp [*]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env Atom := AList (fun (_ : PName) => Types Atom)

instance envDecidableEq {Atom : Type} [DecidableEq Atom] : DecidableEq (Env Atom) :=
  AList.instDecidableEq

abbrev EmptyEnv : Env Atom := (∅ : AList (fun (_ : PName) => Types Atom))

def Env.mk (x : PName) (A : Types Atom) : Env Atom :=
  (List.toAList []).insert x A

def Env.names (Δ : Env Atom) : List (PName) :=
  Δ.keys

-- Order independent equality for environments
@[simp]
def envEq (Δ Γ : Env Atom) : Prop :=
  ∀ (x : PName), Δ.lookup x = Γ.lookup x

-- Eq reflexivity
@[simp]
theorem envEq.refl (Δ : Env Atom) : envEq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
@[simp]
theorem envEq.symm (Δ Γ : Env Atom) (h : envEq Δ Γ) : envEq  Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
@[simp]
theorem envEq.trans (Δ Γ Ε : Env Atom) (h₁ : envEq Δ Γ) (h₂ : envEq Γ Ε) :
  envEq  Δ Ε := fun x => Eq.trans (h₁ x) (h₂ x)

instance {Atom : Type} : Equivalence (@envEq Atom) :=
{ refl := @envEq.refl Atom,
  symm := @envEq.symm Atom,
  trans := @envEq.trans Atom }

-- Missing sorting to make cannonical form
-- Missing disjoint requirement
@[simp]
-- def Env.merge (Δ Γ : Env Atom) [Decidable (Δ.Disjoint Γ)] : Option (Env Atom) :=
--   if Δ.Disjoint Γ then some (Δ ∪ Γ) else none
def Env.merge {Atom : Type u} (Δ Γ : Env Atom) (h : AList.Disjoint Δ Γ) : Env Atom :=
  Δ ∪ Γ

-- identity
@[simp]
theorem mergeEnv.unitR {Atom : Type u} (Δ : Env Atom) :
    Δ.merge EmptyEnv (by intro k ; simp [AList.keys_empty]) = Δ := by
  simp

@[simp]
theorem mergeEnv.unitL {Atom : Type u} (Δ : Env Atom) :
    EmptyEnv.merge Δ (by intro k ; simp [AList.keys_empty]) = Δ := by
  trivial

-- commutivity
@[simp]
theorem mergeEnv.comm (Δ Γ : Env Atom) (h : AList.Disjoint Δ Γ) :
  (Δ.merge Γ h).entries.Perm (Γ.merge Δ (by intro k hk h' ; exact h k h' hk)).entries :=
  AList.union_comm_of_disjoint h

-- associativity
@[simp]
theorem mergeEnv.assoc {Atom : Type u}
  (Δ Γ Ε : Env Atom)
  (hΔΓ : Δ.Disjoint Γ)
  (hΔΓΕ : Δ.Disjoint (Γ ∪ Ε))
  (hΓΕ : Γ.Disjoint Ε)
  (hΕΔΓ : Ε.Disjoint (Δ ∪ Γ)) :
  (Ε.merge (Δ.merge Γ hΔΓ) hΕΔΓ).entries.Perm
  (Δ.merge (Γ.merge Ε hΓΕ) hΔΓΕ).entries := by
  unfold Env.merge
  -- exact AList.union_assoc
  sorry -- The above should work but there is some DecidableEq thing Lean gets stuck on

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv Atom := Finset (Env Atom)

abbrev EmptyHyperEnv : HyperEnv Atom := {}

-- Coercion makes extending a hyperenv with env and merging the same
-- and env1 |ₕ env2 => hyperenv due to envs being lifted to hyperenv
instance : Coe (Env Atom) (HyperEnv Atom) := ⟨fun Γ => {Γ}⟩

-- def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
--   ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def hyperEnv.linearity (𝒢 : HyperEnv Atom) : Prop :=
  -- ∀ Δ ∈ 𝒢, envLinearity Δ ∧                              -- ensure each env is linear
  -- pairwise (fun Δ Γ => AList.Disjoint Δ Γ) 𝒢              -- ensure pairwise env disjointness
  ∀ x ∈ 𝒢, ∀ y ∈ 𝒢, y ≠ x → x.Disjoint y

def HyperEnv.names (𝒢 : HyperEnv Atom) : Finset PName :=
  Finset.fold (· ∪ ·) ∅ (fun Δ => Δ.names.toFinset) 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def hyperLookupTypeOf (𝒢 : HyperEnv Atom) (x : PName) : Option (Types Atom) :=
  (𝒢.toList.find? (fun Δ => (Δ.lookup x).isSome)) >>= fun Δ  => Δ.lookup x

def HyperEnv.disjoint (𝒢 ℋ : HyperEnv Atom) [DecidableEq (Env Atom)] : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  hyperEnv.linearity 𝒢 ∧ hyperEnv.linearity ℋ ∧
  (𝒢 ∩ ℋ).card = 0 ∧
  (HyperEnv.names 𝒢 ∩ HyperEnv.names ℋ) = ∅

-- Order independent equality for hyper-environments
def hyperEnv.Eq (𝒢 ℋ : HyperEnv Atom) : Prop :=
  -- 𝒢 and ℋ must define the same names
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  -- The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  ∀ x ∈ HyperEnv.names 𝒢, hyperLookupTypeOf 𝒢 x = hyperLookupTypeOf ℋ x

-- reflexivity
@[simp]
theorem hyperEnvEq.refl (𝒢 : HyperEnv Atom) : hyperEnv.Eq 𝒢 𝒢 := by
  simp [hyperEnv.Eq]

-- symmetry
@[simp]
theorem hyperEnvEq.symm (𝒢 ℋ : HyperEnv Atom) (h : hyperEnv.Eq 𝒢 ℋ) : hyperEnv.Eq ℋ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- transitivity
@[simp]
theorem hyperEnvEq.trans (𝒢 ℋ 𝒦 : HyperEnv Atom) (h₁ : hyperEnv.Eq 𝒢 ℋ) (h₂ : hyperEnv.Eq ℋ 𝒦) :
  hyperEnv.Eq 𝒢 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ HyperEnv.names ℋ := by rw [← h₁_names]; exact hx
    calc
      hyperLookupTypeOf 𝒢 x = hyperLookupTypeOf ℋ x := h₁_vals x hx
      _    = hyperLookupTypeOf 𝒦 x := h₂_vals x hxH

instance {Atom : Type} : Equivalence (@hyperEnv.Eq Atom) :=
{ refl := @hyperEnvEq.refl Atom,
  symm := @hyperEnvEq.symm Atom,
  trans := @hyperEnvEq.trans Atom }

@[simp]
noncomputable def HyperEnv.merge (𝒢 ℋ : HyperEnv Atom) [DecidableEq (Env Atom)] : HyperEnv Atom :=
  𝒢 ∪ ℋ

-- identity
@[simp]
theorem mergeHyperEnv.unitL (𝒢 : HyperEnv Atom) [DecidableEq (Env Atom)] :
  HyperEnv.merge EmptyHyperEnv 𝒢 = 𝒢 := by
  simp

@[simp]
theorem mergeHyperEnv.unitR (𝒢 : HyperEnv Atom) [DecidableEq (Env Atom)] :
  HyperEnv.merge 𝒢 EmptyHyperEnv = 𝒢 := by
  simp

-- commutative
@[simp]
theorem mergeHyperEnv.comm (𝒢 ℋ : HyperEnv Atom) [DecidableEq (Env Atom)] :
  HyperEnv.merge 𝒢 ℋ = HyperEnv.merge ℋ 𝒢 := by
  simp [Finset.union_comm]

-- associativity
@[simp]
theorem mergeHyperEnv.assoc (𝒢 ℋ 𝒦 : HyperEnv Atom) [DecidableEq (Env Atom)] :
  HyperEnv.merge (HyperEnv.merge 𝒢 ℋ) 𝒦 = HyperEnv.merge 𝒢 (HyperEnv.merge ℋ 𝒦) := by
  simp
----------------------------------------- NOTATION -----------------------------------------

/- PROC -/
notation:80 x "⟦" y "⟧" "." P:80 => Proc.tensor x y P
notation:80 x "⟦" "⟧" "." P:80 => Proc.one x P
notation:80 x "⸨" y "⸩" "." P:80 => Proc.parr x y P
notation:80 x "⸨" "⸩" "." P:80 => Proc.bot x P
notation:60 "𝑣" "⸨" x ", " y "⸩ " P => Proc.cut x y P
notation "𝟘" => Proc.nil
infixr:65 " |ₚ " => Proc.par

/- TYPING -/

-- -- TAKE A LOOK AT THIS COMPARED TO WHAT YOU HAVE:
-- @[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
-- @[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus
-- @[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
-- @[inherit_doc] scoped infix:30 " & " => Proposition.with

-- @[inherit_doc] scoped prefix:95 "!" => Proposition.bang
-- @[inherit_doc] scoped prefix:95 "ʔ" => Proposition.quest

infixr:95 " ⊗ " => Types.tensor
infixr:95 " ⅋ " => Types.parr
notation:100 "𝟙" => Types.one
notation:100 "⊥" => Types.bot
notation:max A "ᗮ" => Types.dual A

/- ENV -/
infixr:90 " ∶ " => Env.mk
infixr:85 "‚ " => Env.merge

/- HYPERENV -/
notation:60 𝒢 "⸨" x "⸩" => hyperLookupTypeOf 𝒢 x
infixr:55 " |ₕ " => HyperEnv.merge

--------------------------------------- TYPING RULES ---------------------------------------

-- inductive Typing : HyperEnv Atom → Proc → Prop where
--   | mix₀ :
--     ----------
--     Typing ∅ 𝟘

--   | mix (𝒢 ℋ : HyperEnv Atom) (P Q : Proc) :
--     Typing 𝒢 P → Typing ℋ Q →
--     --------------------------
--      Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

--   | cut (𝒢 : HyperEnv Atom) (Γ Δ : Env Atom) (P : Proc) (x y : PName) (A : Types Atom) :
--     Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
--     ---------------------------------------
--         Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

--   | tensor (Γ Δ : Env Atom) (P : Proc) (x y : PName) (A B : Types Atom) :
--     Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
--     ---------------------------------
--     Typing (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦y⟧.P)

--   | one (P : Proc) (x : PName) :
--         Typing ∅ P →
--     --------------------
--     Typing (x ∶ 𝟙) (x⟦⟧.P)

--   | parr (Γ : Env Atom) (P : Proc) (x y : PName) (A B : Types Atom) :
--      Typing (Γ‚ y ∶ A‚ x ∶ B) P →
--     -----------------------------
--     Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩.P)

--   | bot (Γ : Env Atom) (P : Proc) (x : PName) :
--           Typing Γ P →
--     ------------------------
--     Typing (Γ‚ x ∶ ⊥) (x⸨⸩.P)

-- notation:50 "⊢ " P " ∷ " T => Typing T P

-- variable (x y z : PName)
-- set_option pp.notation false in -- disable pretty print
-- #check Proc.cut x y (Proc.par (Proc.one x 𝟘) (Proc.bot y (Proc.one z 𝟘)))



-- -- inductive LTS : Type where
-- --   | sorry
















-- ----------------------------------------- EXAMPLES -----------------------------------------

-- -- Latch_xyz example from main.pdf
-- -- TODO: Try and use simp more, try and omit giving explicit types to cut,
-- --       in general try minimizing things given to cut
-- example (x x₁ x₂ y y₁ y₂ z : PName) :
--   ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
--     x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙 := by
--   apply Typing.cut ∅ _ _ _ _ _ (𝟙)
--   rw [mergeHyperEnv.unitL, mergeEnv.comm]
--   conv => lhs ; rhs ; rhs ; rw [mergeEnv.assoc]
--   apply Typing.cut _ _ _ _ _ _ (𝟙)
--   apply Typing.mix
--   · apply Typing.bot
--     apply Typing.one
--     exact Typing.mix₀
--   · apply Typing.mix
--     · rw [mergeEnv.comm]
--       apply Typing.bot
--       apply Typing.one
--       exact Typing.mix₀
--     · conv => lhs ; rhs ; rw [mergeEnv.comm, ←mergeEnv.assoc] ; lhs ; rw [mergeEnv.comm]
--       apply Typing.bot
--       apply Typing.bot
--       apply Typing.one
--       exact Typing.mix₀
