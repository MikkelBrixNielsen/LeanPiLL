import PiLL.Framework.Model.Base

-- abbrev Atom := Nat

-- structure TVar where
--   name : Nat
-- deriving Repr, DecidableEq, BEq

-- instance : ToString TVar where
--   toString t := reprStr t

-- -- FIXME: Probably don't need zero or top
-- inductive Types : Type where
--   | atom      (a : Atom)                -- named type, like A, B, ...
--   | atomDual  (a : Atom)                -- dual of a named type
--   | var       (v : TVar)                -- type variable
--   | varDual   (v : TVar)                -- dual type variables
--   | one                                 -- 𝟙 (empty output, unit for ⨂)
--   | bot                                 -- ⊥ (empty send, unit for ⅋)
--   | zero                                -- 𝟘 (unit for ⊕)
--   | top                                 -- ⊤ (unit for &)
--   | tensor    (A B : Types)             -- A ⨂ B (send)
--   | parr      (A B : Types)             -- A ⅋ B (receive)
--   | oplus     (A B : Types)             -- A ⊕ B (select A or B)
--   | amp       (A B : Types)             -- A & B (Offer A or B)
--   | bang      (A : Types)               -- !A (server accept)
--   | quest     (A : Types)               -- ?A (client request)
--   | forall_   (v : TVar) (A : Types)    -- ∀X.A (universal type input)
--   | exists_   (v : TVar) (A : Types)    -- ∃X.A (existential type output)
-- deriving DecidableEq, BEq

-- infixr:90 " ⨂ " => Types.tensor
-- infixr:90 " ⊕ " => Types.oplus
-- infixr:90 " ⅋ " => Types.parr
-- infixr:90 " & " => Types.amp

-- instance : Zero Types := ⟨Types.zero⟩
-- instance : One Types := ⟨Types.one⟩
-- instance : Top Types := ⟨Types.top⟩
-- instance : Bot Types := ⟨Types.bot⟩

-- prefix:95 "??" => Types.quest
-- prefix:95 "!!" => Types.bang

-- FIXME: Needs to bind tighter to the first type after "․" s.t. ∀X.A ⨂ A => (∀X.A) ⨂ A
-- notation:max "∃" v "․" A => Types.exists_ v A
-- notation:max "∀" v "․" A => Types.forall_ v A

-- private def reprTypesAux : Types → Nat → String
--   | .atom a, _ => s!"A{a}"
--   | .atomDual a, _ => s!"A{a}ᗮ"
--   | .var v, _ => s!"V{v}"
--   | .varDual v, _ => s!"V{v}ᗮ"
--   | .one, _ => "1"
--   | .bot, _ => "⊥"
--   | .zero, _ => "0" -- FIXME: Probably don't need
--   | .top, _ => "⊤"  -- FIXME: Probably don't need
--   | .tensor A B, _ => s!"({reprTypesAux A 0} ⨂ {reprTypesAux B 0})"
--   | .parr A B, _ => s!"({reprTypesAux A 0} ⅋ {reprTypesAux B 0})"
--   | .oplus A B, _ => s!"({reprTypesAux A 0} ⊕ {reprTypesAux B 0})"
--   | .amp A B, _ => s!"({reprTypesAux A 0} & {reprTypesAux B 0})"
--   | .bang A, _ => s!"!!{reprTypesAux A 0}"
--   | .quest A, _ => s!"??{reprTypesAux A 0}"
--   | .forall_ v A, _ => s!"∀{v}:{reprTypesAux A 0}"
--   | .exists_ v A, _ => s!"∃{v}:{reprTypesAux A 0}"

-- instance : Repr Types where
--   reprPrec A _ := reprTypesAux A 0

-- instance : ToString Types where
--   toString t := reprStr t

abbrev Atom := Nat
abbrev FTVar := Nat
abbrev BTVar := Nat

inductive TVar : Type
  | free    (x : FTVar)
  | bound   (x : BTVar)
deriving DecidableEq, Repr

inductive Types : Type where
  | atom        (a : Atom)
  | atomDual    (a : Atom)
  | var         (v : TVar)
  | varDual     (v : TVar)
  | one
  | bot
  | tensor      (A B : Types)
  | parr        (A B : Types)
  | oplus       (A B : Types)
  | amp         (A B : Types)
  | bang        (A : Types)
  | quest       (A : Types)
  | forall_     (A : Types)           -- Binds 1 Type Variable
  | exists_     (A : Types)           -- Binds 1 Type Variable
deriving DecidableEq, BEq, Repr

infixr:90 " ⨂ " => Types.tensor
infixr:90 " ⊕ " => Types.oplus
infixr:90 " ⅋ " => Types.parr
infixr:90 " & " => Types.amp

instance : One Types := ⟨Types.one⟩
instance : Bot Types := ⟨Types.bot⟩

prefix:95 "??" => Types.quest
prefix:95 "!!" => Types.bang

prefix:max "∃․" => Types.exists_
prefix:max "∀․" => Types.forall_

-- def openTVar (k : Nat) (u : TVar) : TVar → TVar
--   | TVar.bound i => if i = k then u else TVar.bound i
--   | v => v

-- def openType (k : Nat) (u : TVar) : Types → Types
--   | .atom a => .atom a
--   | .atomDual a => .atomDual a
--   | .var v => .var (openTVar k u v)
--   | .varDual v => .varDual (openTVar k u v)
--   | .one => .one
--   | .bot => .bot
--   | .tensor A B => .tensor (openType k u A) (openType k u B)
--   | .parr A B => .parr (openType k u A) (openType k u B)
--   | .oplus A B => .oplus (openType k u A) (openType k u B)
--   | .amp A B => .amp (openType k u A) (openType k u B)
--   | .bang A => .bang (openType k u A)
--   | .quest A => .quest (openType k u A)
--   | .forall_ A => .forall_ (openType (k+1) u A)
--   | .exists_ A => .exists_ (openType (k+1) u A)

-- def openType0 (u : TVar) (A : Types) : Types :=
--   openType 0 u A

def TVar.lc : Nat → TVar → Prop
  | _, .free _ => True
  | k, .bound i => i < k

def Types.lc : Nat → Types → Prop
  | _, .atom _      => True
  | _, .atomDual _  => True
  | k, .var v       => TVar.lc k v
  | k, .varDual v   => TVar.lc k v
  | _, .one         => true
  | _, .bot         => true
  | k, .tensor A B  => A.lc k ∧ B.lc k
  | k, .parr A B    => A.lc k ∧ B.lc k
  | k, .oplus A B   => A.lc k ∧ B.lc k
  | k, .amp A B     => A.lc k ∧ B.lc k
  | k, .bang A => A.lc k
  | k, .quest A => A.lc k
  | k, .forall_ A => A.lc (k+1)
  | k, .exists_ A => A.lc (k+1)

def Types.lc_0 : Types → Prop := Types.lc 0

def Types.pos : Types → Prop
  | .atom _ => True
  | .var _ => True
  | .one => True
  -- | .zero => True
  | .tensor _ _ => True
  | .oplus _ _ => True
  | .bang _ => True
  -- | .exists_ _ _ => True
  | .exists_ _ => True
  | _ => False

def Types.neg : Types → Prop
  | .atomDual _ => True
  | .varDual _ => True
  | .bot => True
  -- | .top => True
  | .parr _ _ => True
  | .amp _ _ => True
  | .quest _ => True
  -- | .forall_ _ _ => True
  | .forall_ _ => True
  | _ => False

instance Types.positive_decidable (A : Types) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negative_decidable (A : Types) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

def Types.dual : Types → Types
  | .atom a       => .atomDual a
  | .atomDual a   => .atom a
  | .var v        => .varDual v
  | .varDual v    => .var v
  | .one          => .bot
  | .bot          => .one
  -- | .zero         => .top
  -- | .top          => .zero
  | .tensor A B   => .parr (dual A) (dual B)
  | .parr A B     => .tensor (dual A) (dual B)
  | .oplus A B    => .amp (dual A) (dual B)
  | .amp A B      => .oplus (dual A) (dual B)
  | .bang A       => .quest (dual A)
  | .quest A      => .bang (dual A)
  -- | .forall_ v A  => .exist_ v (dual A)
  -- | .exists_ v A   => .forall_ v (dual A)
  | .forall_ A  => .exists_ (dual A)
  | .exists_ A   => .forall_ (dual A)

postfix:max "ᗮ" => Types.dual

theorem Types.dual_neq (A : Types) : A ≠ Aᗮ := by
  cases A <;> simp [dual]

theorem Types.dual_inj (A B : Types) : Aᗮ = Bᗮ ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem Types.dual_involution (A : Types) : Aᗮᗮ = A := by
  induction A <;> simp [Types.dual, *]

def Types.linImpl (A B : Types) : Types := Aᗮ ⅋ B
infix:90 " ⊸ " => Types.linImpl

def Types.freeTypes : Types → Finset TVar
  | .atom _ | .atomDual _ | .one | .bot /-| .zero | .top-/ => ∅
  | .var v        => {v}
  | .varDual v    => {v}
  | .tensor A B   => A.freeTypes ∪ B.freeTypes
  | .parr A B     => A.freeTypes ∪ B.freeTypes
  | .oplus A B    => A.freeTypes ∪ B.freeTypes
  | .amp A B      => A.freeTypes ∪ B.freeTypes
  | .bang A       => A.freeTypes
  | .quest A      => A.freeTypes
  -- | .forall_ v A  => A.freeTypes \ {v}
  -- | .exist_ v A   => A.freeTypes \ {v}
  | .forall_ A  => A.freeTypes
  | .exists_ A   => A.freeTypes

attribute [simp] Types.freeTypes

def Types.isServerUsable : Types → Prop
  | .quest _  => True
  | .bang _   => True
  | _         => False

-- d used as cutoff depth, variables < d are locally bound
-- c is correction / shift amount
def TVar.shift (d c : Nat) : TVar → TVar
  | .bound i => if i < d then .bound i else .bound (i + c)
  | .free n => .free n

instance : HasShiftTypes TVar where shift v d c := TVar.shift d c v

def Types.shift (d c : Nat) : Types → Types
  | .var v        => .var (v.shift d c)
  | .varDual v    => .varDual (v.shift d c)
  | .forall_ A    => .forall_ (A.shift (d + 1) c)          -- binds 1
  | .exists_ A    => .exists_ (A.shift (d + 1) c)          -- binds 1
  | .tensor A B   => .tensor (A.shift d c) (B.shift d c)
  | .parr A B     => .parr (A.shift d c) (B.shift d c)
  | .quest A      => .quest (A.shift d c)
  | .bang A       => .bang (A.shift d c)
  | .amp A B      => .amp (A.shift d c) (B.shift d c)
  | .oplus A B    => .oplus (A.shift d c) (B.shift d c)
  | t             => t -- one | bot | atom | atomDual (Don't have Types to shift)

instance : HasShiftTypes Types where shift T d c := Types.shift d c T

-- Eager shifting
-- k act as target index s.t. A is inserted at depth k, binderes shfit k by 1 to ensure
-- when depth k is reached A can be inserted safely
-- if i == k, target depth reached insert A
-- if i > k, outside binder => decrement to compress an account for i == k being explicit now
-- if i < k, inside binder do nothing => keep i

def Types.subst (A : Types) (k : Nat) : Types → Types
  | .var (.bound i) =>
      if i == k then A
      else if i > k then .var (.bound (i - 1))
      else .var (.bound i)
  | .varDual (.bound i) =>
      if i == k then (.dual A)
      else if i > k then .varDual (.bound (i - 1))
      else .varDual (.bound i)
  | .var (.free i)        => .var (.free i)       -- don't touch free
  | .varDual (.free i)    => .varDual (.free i)   -- don't touch free
  | .forall_ B            => .forall_ (subst (shift 0 1 A) (k + 1) B)
  | .exists_ B            => .exists_ (subst (shift 0 1 A) (k + 1) B)
  | .tensor L R           => .tensor (subst A k L) (subst A k R)
  | .parr L R             => .parr (subst A k L) (subst A k R)
  | .quest B              => .quest (subst A k B)
  | .bang B               => .bang (subst A k B)
  | .amp L R              => .amp (subst A k L) (subst A k R)
  | .oplus L R            => .oplus (subst A k L) (subst A k R)
  | t                     => t -- one | bot | atom | atomDual (Don't have Types to subst)

instance : HasSubst Types Types Nat where subst B A k := Types.subst A k B

lemma Types.lc_dual {n : Nat} {A : Types} :
  A.lc n ↔  Aᗮ.lc n := by
  induction A generalizing n <;>
  simp_all [Types.lc, Types.dual]

lemma Types.lc_shift_c_inv {n d c : Nat} {A : Types} :
  (A ↑ᵗ d, c).lc (n + c + d) ↔ A.lc (n + d) := by
  induction A generalizing n d c

  all_goals (
    simp_all [HasShiftTypes.shift, Types.shift, Types.lc]
  )

  case forall_ ih | exists_ ih => apply ih (d := d + 1)

  case var v | varDual v =>
    cases v with
    | bound i =>
      constructor
      · intro h
        simp_all [TVar.lc, TVar.shift]
        split_ifs at h
        case pos hlt =>
          simp at h
          apply Nat.lt_of_lt_of_le hlt
          apply Nat.le_add_left
        case neg hge =>
          simp_all
          rw [Nat.add_assoc n c d, Nat.add_comm c d, ← Nat.add_assoc] at h
          apply Nat.lt_of_add_lt_add_right h
      · intro h
        simp_all [TVar.lc, TVar.shift]
        split_ifs
        case pos hlt =>
          simp
          apply Nat.lt_of_lt_of_le h
          rw [Nat.add_assoc, Nat.add_comm c d, ← Nat.add_assoc]
          apply Nat.le_add_right
        case neg hge =>
          simp_all
          rw [Nat.add_assoc n c d, Nat.add_comm c d, ← Nat.add_assoc]
          simp_all

    | free _ => simp_all [TVar.lc, TVar.shift]

-- FIXME: Not used?
lemma Types.lc_le {n m : Nat} {A : Types} (h : n ≤ m) :
  A.lc n → A.lc m := by
  intro hlc
  induction A generalizing n m <;> (
    simp_all [Types.lc]
  )

  case var v | varDual v =>
    cases v with
    | bound i => grind [TVar.lc]
    | free _ => simp [TVar.lc]

  case forall_ ih | exists_ ih =>
    exact ih (n := n + 1) (m := m + 1) (Nat.add_one_le_add_one_iff.mpr h) hlc

  case tensor ihA ihB | parr ihA ihB | oplus ihA ihB | amp ihA ihB =>
    exact ⟨ihA h hlc.1, ihB h hlc.2⟩

  case quest ih | bang ih =>
    exact ih h hlc

lemma Types.lc_shift {n d c : Nat} {A : Types} :
  A.lc n → (A ↑ᵗ d, c).lc (n + c) := by
  induction A generalizing n d c <;> (
    intro h
    simp_all [HasShiftTypes.shift, Types.shift, TVar.shift, Types.lc, TVar.lc]
  )

  case var v | varDual v =>
    cases v <;> simp ; split_ifs <;> simp_all [Nat.lt_add_right]

  case forall_ ih | exists_ ih =>
    have := ih (n := n + 1) (d := d + 1) (c := c) h
    rw [Nat.add_assoc, Nat.add_comm 1 _, ← Nat.add_assoc] at this
    exact this

lemma Types.lc_shift_0 {n : Nat} {A : Types} :
  A.lc n → (A ↑ᵗ 0, 1).lc (n + 1) := by
  intro h ; apply Types.lc_shift h

lemma Types.lc_subst_inv {n k : Nat} {A B : Types} (hA : A.lc (n + k)) :
   B{A // k}.lc (n + k) ↔ B.lc (n + k + 1) := by
  induction B generalizing n k A

  all_goals (
    simp_all [HasSubst.subst, Types.subst, Types.lc]
  )

  case forall_ B ih | exists_ B ih =>
    exact ih (k := k + 1) (Types.lc_shift_0 hA)

  case var v =>
    cases v with
    | bound i =>
      simp [Types.subst, TVar.lc]
      split_ifs <;> constructor <;> (intros ; try grind [Types.lc, TVar.lc])
    | free _ => simp_all [Types.subst, Types.lc, TVar.lc]

  case varDual v =>
    cases v with
    | bound i =>
      simp [Types.subst, TVar.lc]
      split_ifs <;> constructor <;> (intros ; try grind [Types.lc, TVar.lc])
      case pos => exact (Types.lc_dual).mp hA
    | free _ => simp_all [Types.subst, Types.lc, TVar.lc]

lemma Types.lc_subst_inv_0 {n : Nat} {A B : Types} :
  A.lc n → ((B{A // #T}).lc n ↔ B.lc (n + 1)) := by
  intro hA
  exact Types.lc_subst_inv (k := 0) hA

lemma Types.lc_shift_inv {n d : Nat} {A : Types} :
  (A ↑ᵗ d, 1).lc (n + d + 1) ↔ A.lc (n + d) := by
  induction A generalizing n d
  all_goals (
    simp_all [Types.lc, HasShiftTypes.shift, Types.shift]
  )

  case var v | varDual v =>
    cases v with
    | bound i =>
      simp [TVar.shift, TVar.lc]
      split_ifs with hle
      · simp
        constructor
        · simp_all [Nat.lt_of_lt_of_le hle]
        · simp_all [Nat.lt_succ_of_lt]
      · simp

    | free i => simp_all [TVar.lc, TVar.shift]

  case forall_ ihA | exists_ ihA =>
    apply ihA (d := d + 1)

lemma Types.lc_shift_inv_0 {n : Nat} {A : Types} :
  A⁺ᵗ.lc (n + 1) ↔ A.lc n := Types.lc_shift_inv (d := 0)

lemma Types.lc_shift_comm {A : Types} {d m n : Nat} :
  (A ↑ᵗ d, m) ↑ᵗ d, n = (A ↑ᵗ d, n) ↑ᵗ d, m := by
  induction A generalizing d m n

  case atom | atomDual | one | bot | tensor | parr | oplus | bang =>
    simp_all [HasShiftTypes.shift, Types.shift]

  case amp ihA ihB =>
    simp [HasShiftTypes.shift, Types.shift]
    exact ⟨ihA, ihB⟩

  case quest ih | forall_ ih | exists_ ih=>
    simp [HasShiftTypes.shift, Types.shift]
    exact ih

  case var v | varDual v =>
    simp [HasShiftTypes.shift, Types.shift]
    cases v with
    | bound i => simp [TVar.shift] ; grind
    | free _ => simp [TVar.shift]

lemma Types.lc_shift_comm_0 {A : Types} {k : Nat} :
  A⁺ᵗ ↑ᵗ k = (A ↑ᵗ k)⁺ᵗ := Types.lc_shift_comm (d := 0)

lemma Types.shift_add {A : Types} {d a b : Nat} :
  (A ↑ᵗ d, a) ↑ᵗ d, b = A ↑ᵗ d, (a + b) := by
  induction A generalizing d a b <;> (
    simp [HasShiftTypes.shift, Types.shift]
  )

  case var v | varDual v =>
    cases v with
    | bound i => grind [TVar.shift]
    | free _ => simp [TVar.shift]

  case forall_ ih | exists_ ih | bang ih | quest ih=> exact ih

  case tensor ihA ihB | parr ihA ihB | oplus ihA ihB | amp ihA ihB =>
    exact ⟨ihA, ihB⟩

lemma Types.shift_accum {A : Types} {d a b : Nat} :
  (A ↑ᵗ d, a) ↑ᵗ (d + a), b = A ↑ᵗ d, (a + b) := by
  induction A generalizing d a b <;> (
    simp [HasShiftTypes.shift, Types.shift]
  )

  case var v | varDual v =>
    cases v with
    | bound i => grind [TVar.shift]
    | free _ => simp [TVar.shift]

  case forall_  ih | exists_ ih =>
    rw [Nat.add_assoc, Nat.add_comm a 1, ← Nat.add_assoc]
    exact ih (d := d + 1) (a := a) (b := b)

  case tensor ihA ihB | parr ihA ihB | oplus ihA ihB | amp ihA ihB =>
    exact ⟨ihA, ihB⟩

  case bang ih | quest ih => exact ih

lemma Types.shift_accum_0 {A : Types} {a b : Nat} :
  (A ↑ᵗ a) ↑ᵗ a, b = A ↑ᵗ (a + b) := by
  change (A ↑ᵗ 0, a) ↑ᵗ (a + 0), b = A ↑ᵗ (a + b)
  rw [Nat.add_comm a 0]
  exact Types.shift_accum

lemma Types.shift_dual_comm {A : Types} {d c : Nat} :
  (Aᗮ ↑ᵗ d, c) = (A ↑ᵗ d, c)ᗮ := by
  induction A generalizing d c <;> (
    simp_all [HasShiftTypes.shift, Types.shift, Types.dual, TVar.shift]
  )

lemma Types.shift_comm {A : Types} {d c i : Nat} :
  (A ↑ᵗ i, 1) ↑ᵗ (d + 1 + i), c = (A ↑ᵗ (d + i), c) ↑ᵗ i, 1 := by
  induction A generalizing d c i

  case atom | atomDual | one | bot =>
    simp_all [HasShiftTypes.shift, Types.shift]

  case tensor ihA ihB | parr ihA ihB | oplus ihA ihB | amp ihA ihB =>
    simp [HasShiftTypes.shift, Types.shift]
    exact ⟨ihA, ihB⟩

  case bang A ih | quest A ih =>
    simp [HasShiftTypes.shift, Types.shift]
    exact ih

  case var v | varDual v =>
    simp [HasShiftTypes.shift, Types.shift]
    cases v with
    | bound i => grind [TVar.shift]
    | free _ => simp [TVar.shift]

  case forall_ ih | exists_ ih =>
    simp [HasShiftTypes.shift, Types.shift]
    exact ih (d := d) (c := c) (i := i + 1)

lemma Types.shift_comm_0 {A : Types} {d c : Nat} :
 (A.shift 0 1).shift (d + 1) c = (A.shift d c).shift 0 1 := by
  exact Types.shift_comm (i := 0)

lemma Types.shift_subst_comm {A B : Types} {d c : Nat} :
  B{A // d} ↑ᵗ d, c = (B ↑ᵗ (d + 1), c){A ↑ᵗ d, c // d} := by
  induction B generalizing A d c <;> (
    simp [HasShiftTypes.shift, HasSubst.subst, Types.subst, Types.shift]
  )

  case tensor ihA ihB | parr ihA ihB | oplus ihA ihB | amp ihA ihB =>
    exact ⟨ihA, ihB⟩

  case bang ih | quest ih =>
    exact ih

  case var v =>
    cases v with
    | bound x =>
      by_cases h : x = d
      · grind [Types.subst, TVar.shift]
      · simp [Types.subst, TVar.shift]
        grind [Types.subst, Types.shift, TVar.shift]
    | free _ => simp [Types.shift, Types.subst, TVar.shift]

  case varDual v =>
    cases v with
    | bound x =>
      by_cases h : x = d
      · simp_all [Types.subst, TVar.shift]
        exact Types.shift_dual_comm
      · simp [Types.subst, TVar.shift]
        grind [Types.subst, Types.shift, TVar.shift]
    | free _ => simp [Types.shift, Types.subst, TVar.shift]

  case forall_ B ih | exists_ B ih =>
    rw [← Types.shift_comm_0 (A := A) (d := d) (c := c)]
    exact ih (A := A⁺ᵗ) (d := d + 1) (c := c)















-- FIXME: Should aviod capture
-- (Constriants on Typing rules handle this but maybe they shouldn't)
-- def Types.subst (T R : Types) (X : TVar) : Types :=
--   match T with
--   | .atom a => .atom a
--   | .atomDual a => .atomDual a
--   | .var v => if v = X then R else .var v
--   | .varDual v => if v = X then Rᗮ else .varDual v
--   | .one => .one
--   | .bot => .bot
--   -- | .zero => .zero  -- FIXME: type probably not needed
--   -- | .top => .top    -- FIXME: type probably not needed
--   | .tensor A B => .tensor (A.subst R X) (B.subst R X)
--   | .parr A B => .parr (A.subst R X) (B.subst R X)
--   | .oplus A B => .oplus (A.subst R X) (B.subst R X)
--   | .amp A B => .amp (A.subst R X) (B.subst R X)
--   | .bang A => .bang (A.subst R X)
--   | .quest A => .quest (A.subst R X)
--   | .forall_ v A => if v = X then .forall_ v A else .forall_ v (A.subst R X)
--   | .exist_ v A => if v = X then .exist_ v A else .exist_ v (A.subst R X)

-- instance : HasSubst Types Types TVar where subst := Types.subst

-- @[simp]
-- lemma Types.subst_dual (A B : Types) (X : TVar) : Bᗮ{A // X} = B{A // X}ᗮ := by
--   induction B <;> simp [dual, HasSubst.subst, subst] <;> try split
--   all_goals try simp_all [dual, HasSubst.subst, dual_involution]

-- @[simp] lemma Types.isServerUsable_subst (T : Types) (A : Types) (X : TVar)
--   (h : T.isServerUsable) : (T{A // X}).isServerUsable := by
--   cases T <;> simp [HasSubst.subst, Types.subst, Types.isServerUsable] at h ⊢

-- lemma Types.subst_eq_self {T A : Types} {X : TVar} {hft : X ∉ T.freeTypes} :
--   T.subst A X = T := by
--   induction T <;> simp_all [Types.subst, Types.freeTypes, ← ne_eq]

--   case var | varDual=>
--     intro h
--     subst h
--     contradiction

--   case forall_ ih | exist_ ih =>
--     split_ifs with h
--     · subst h ; rfl
--     · simp_all only [forall_.injEq, exist_.injEq, true_and, ← ne_eq]
--       apply ih
--       intro h_contra
--       simp [h_contra] at hft
--       subst hft
--       contradiction

-- lemma Types.freeTypes_dual_eq (T : Types) : T.dual.freeTypes = T.freeTypes := by
--   induction T <;> simp_all [Types.freeTypes, Types.dual]

-- @[simp] lemma Types.not_mem_ft_subst {T A : Types} {X Y : TVar}
--   (hT : Y ∉ T.freeTypes) (hA : Y ∉ A.freeTypes) (hneq : Y ≠ X) :
--   Y ∉ (T.subst A X).freeTypes := by
--   induction T <;> simp_all [Types.subst, Types.freeTypes, ← ne_eq]

--   case var =>
--     split_ifs with h
--     · exact hA
--     · simp [Types.freeTypes] ; exact hT

--   case varDual =>
--     split_ifs with h
--     · simp [Types.freeTypes_dual_eq] ; exact hA
--     · simp [Types.freeTypes] ; exact hT

--   case forall_ A' ih | exist_ A' ih =>
--     split_ifs with h1
--     · simp [Types.freeTypes]
--       intro hin
--       have heq : Y = X := by
--         rw [← h1]
--         apply hT hin
--       contradiction
--     · simp only [Types.freeTypes, Finset.mem_sdiff, Finset.mem_singleton]
--       intro h2
--       have hog : Y ∈ A'.freeTypes := by
--         by_contra hc
--         apply ih at hc
--         exact hc h2.1
--       apply hT at hog
--       exact h2.2 hog

-- lemma Types.subst_subst (T A B : Types) (X : TVar) :
--   (T.subst A X).subst B X = T.subst (A.subst B X) X := by
--   induction T generalizing A B <;> simp_all [Types.subst]

--   case var | varDual =>
--     split_ifs with h
--     · (try erw [← Types.subst_dual]) ; rfl
--     · simp [Types.subst]
--       intro a
--       contradiction

--   case forall_ ih | exist_ ih =>
--     split_ifs with h
--     · simp [Types.subst]
--     · simp [Types.subst]
--       simp [h]
--       apply ih

-- @[simp] lemma Types.subst_eq_self_of_not_mem (T A : Types) (X : TVar)
--   (h : X ∉ T.freeTypes) : T.subst A X = T := by
--   induction T <;> simp_all [Types.subst, Types.freeTypes]
--   case var | varDual =>
--     intro h
--     subst h
--     contradiction

--   case forall_ ih | exist_ ih =>
--     split_ifs with h1
--     · subst h1 ; rfl
--     · congr
--       apply ih
--       intro hin
--       apply h at hin
--       rw [hin] at h1
--       contradiction
