----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
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

abbrev Atom := Nat

inductive Types : Type where
  | atom      (a : Atom)      -- named type, like A, B, ...
  | atomDual  (a : Atom)      -- dual of a named type
  | tensor    (A B : Types)   -- t₁ ⊗ t₂ (send)
  | parr      (A B : Types)   -- t₁ ⅋ t₂ (receive)
  | one                       -- 𝟙 (empty output, unit for ⊗)
  | bot                       -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

def Types.pos : Types → Prop
  | atom _ => True
  | one => True
  | tensor _ _ => True
  -- | oplus _ _ => True
  -- | bang _ => True
  -- | zero => True
  | _ => False

def Types.neg : Types → Prop
  | atomDual _ => True
  | bot => True
  | parr _ _ => True
  -- | top => True
  -- | .with _ _ => True
  -- | quest _ => True
  | _ => False

instance Types.posDecidable (A : Types) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negDecidable (A : Types) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

@[simp]
def Types.dual : Types → Types
| .tensor A B => .parr (dual A) (dual B)
| .parr A B   => .tensor (dual A) (dual B)
| .one        => .bot
| .bot        => .one
| .atom a     => .atomDual a
| .atomDual a => .atom a

@[simp]
theorem Types.dual.neq (A : Types) : A ≠ dual A := by
  cases A <;> simp [dual]

@[simp]
theorem dual.inj (A B : Types) : Types.dual A = Types.dual B ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem dual.involution (A : Types) : Types.dual (Types.dual A) = A := by
  induction A <;> simp [*]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env := Finset (PName × Types)

abbrev EmptyEnv : Env := ∅

def Env.mk (x : PName) (A : Types) : Env :=
  {(x, A)}

def Env.linear (Δ : Env) : Prop :=
  (Δ.image Prod.fst).card = Δ.card

def Env.names (Δ : Env) : Finset (PName) :=
  (Δ.image Prod.fst)

def Env.disjoint (Δ Γ : Env) : Prop :=
  (Δ.image Prod.fst ∩ Γ.image Prod.fst).card = 0

noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
  -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

-- Order independent equality for environments
def Env.Eq (Δ Γ : Env) : Prop :=
  ∀ x : (PName), Δ.lookup x = Γ.lookup x

-- Eq reflexivity
@[simp]
theorem Env.Eq_refl (Δ : Env) : Env.Eq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
@[simp]
theorem Env.Eq_symm (Δ Γ : Env) (h : Env.Eq Δ Γ) : Env.Eq Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
@[simp]
theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Env.Eq Δ Γ) (h₂ : Env.Eq Γ Ε) : Env.Eq Δ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence Env.Eq :=
⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

-- identity
@[simp]
theorem Env.merge_unitR (Δ : Env) : Δ.merge EmptyEnv = Δ := by
  simp [Env.merge]

@[simp]
theorem Env.merge_unitL (Δ : Env) : Env.merge EmptyEnv Δ = Δ := by
  simp [Env.merge]

-- commutivity
-- theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Γ Δ := by
@[simp]
theorem Env.merge_comm (Δ Γ : Env) : Δ.merge Γ = Γ.merge Δ := by
  simp [Env.merge]
  simp [Finset.union_comm]

-- associativity
@[simp]
theorem Env.merge_assoc (Δ Γ Ε : Env) : (Δ.merge Γ).merge Ε = Δ.merge (Γ.merge Ε) := by
  simp [Env.merge]

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := {}

-- Coercion makes extending a hyperenv with env and merging the same
-- and env1 |ₕ env2 => hyperenv due to envs being lifted to hyperenv
instance : Coe Env HyperEnv := ⟨fun Γ => {Γ}⟩

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
  ∀ Δ ∈ 𝒢, Δ.linear ∧                               -- ensure each env is linear
  pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
  Finset.fold (· ∪ ·) ∅ Env.names 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
  (𝒢.toList.find? (fun Δ => Δ.lookup x ≠ none)) >>= fun Δ  => Δ.lookup x

def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  𝒢.linear ∧ ℋ.linear ∧
  (𝒢 ∩ ℋ).card = 0 ∧
  (HyperEnv.names 𝒢 ∩ HyperEnv.names ℋ) = ∅

-- Order independent equality for hyper-environments
def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
  -- 𝒢 and ℋ must define the same names
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  -- The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  ∀ x ∈ HyperEnv.names 𝒢, 𝒢.lookup x = ℋ.lookup x

-- reflexivity
@[simp]
theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : HyperEnv.Eq 𝒢 𝒢 := by
  simp [HyperEnv.Eq]

-- symmetry
@[simp]
theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : HyperEnv.Eq 𝒢 ℋ) : HyperEnv.Eq ℋ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- transitivity
@[simp]
theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : HyperEnv.Eq 𝒢 ℋ) (h₂ : HyperEnv.Eq ℋ 𝒦) :
  HyperEnv.Eq 𝒢 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
    calc
      𝒢.lookup x = ℋ.lookup x := h₁_vals x hx
      _    = 𝒦.lookup x := h₂_vals x hxH

instance : Equivalence HyperEnv.Eq :=
⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

noncomputable def HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

-- identity
@[simp]
theorem mergeHyperEnv.unitL (𝒢 : HyperEnv) : HyperEnv.merge EmptyHyperEnv 𝒢 = 𝒢 := by
  simp [HyperEnv.merge]

@[simp]
theorem mergeHyperEnv.unitR (𝒢 : HyperEnv) : HyperEnv.merge 𝒢 EmptyHyperEnv = 𝒢 := by
  simp [HyperEnv.merge]

-- commutative
@[simp]
theorem mergeHyperEnv.comm (𝒢 ℋ : HyperEnv) : HyperEnv.merge 𝒢 ℋ = HyperEnv.merge ℋ 𝒢 := by
  simp [HyperEnv.merge, Finset.union_comm]

-- associativity
@[simp]
theorem mergeHyperEnv.assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  HyperEnv.merge (HyperEnv.merge 𝒢 ℋ) 𝒦 = HyperEnv.merge 𝒢 (HyperEnv.merge ℋ 𝒦) := by
  simp [HyperEnv.merge]

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
infixr:95 " ⊗ " => Types.tensor
infixr:95 " ⅋ " => Types.parr
notation:100 "𝟙" => Types.one
notation:100 "⊥" => Types.bot
notation:max A "ᗮ" => Types.dual A

/- ENV -/
infixr:90 " ∶ " => Env.mk
infixr:85 "‚ " => Env.merge

/- HYPERENV -/
notation:60 𝒢 "⸨" x "⸩" => HyperEnv.lookup 𝒢 x
infixr:55 " |ₕ " => HyperEnv.merge

--------------------------------------- TYPING RULES ---------------------------------------

inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
    ----------
    Typing ∅ 𝟘

  | mix (𝒢 ℋ : HyperEnv) (P Q : Proc) :
    Typing 𝒢 P → Typing ℋ Q →
    --------------------------
     Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types) :
    Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
    ---------------------------------------
        Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor (Γ Δ : Env) (P : Proc) (x y : PName) (A B : Types) :
    Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
    ---------------------------------
    Typing (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦y⟧.P)

  | one (P : Proc) (x : PName) :
        Typing ∅ P →
    --------------------
    Typing (x ∶ 𝟙) (x⟦⟧.P)

  | parr (Γ : Env) (P : Proc) (x y : PName) (A B : Types) :
     Typing (Γ‚ y ∶ A‚ x ∶ B) P →
    -----------------------------
    Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩.P)

  | bot (Γ : Env) (P : Proc) (x : PName) :
          Typing Γ P →
    ------------------------
    Typing (Γ‚ x ∶ ⊥) (x⸨⸩.P)

notation:50 "⊢ " P " ∷ " T => Typing T P




-- inductive πLL : Type where
--   | sorry









---------------------------------------- EXAMPLES ----------------------------------------

-- Latch_xyz example from main.pdf
-- TODO: Try and use simp more, try and omit giving explicit types to cut,
--       in general try minimizing things given to cut
example (x x₁ x₂ y y₁ y₂ z : PName) :
  ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
    x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙 := by
  apply Typing.cut ∅ _ _ _ _ _ (𝟙)
  rw [mergeHyperEnv.unitL, Env.merge_comm]
  conv => lhs ; rhs ; rhs ; rw [Env.merge_assoc]
  apply Typing.cut _ _ _ _ _ _ (𝟙)
  apply Typing.mix
  · apply Typing.bot
    apply Typing.one
    exact Typing.mix₀
  · apply Typing.mix
    · rw [Env.merge_comm]
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀
    · conv => lhs ; rhs ; rw [Env.merge_comm, ←Env.merge_assoc] ; lhs ; rw [Env.merge_comm]
      apply Typing.bot
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀
