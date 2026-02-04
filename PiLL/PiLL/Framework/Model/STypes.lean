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

notation:max "∃․" A => Types.exists_ A
notation:max "∀․" A => Types.forall_ A

def openTVar (k : Nat) (u : TVar) : TVar → TVar
  | TVar.bound i => if i = k then u else TVar.bound i
  | v => v

def openType (k : Nat) (u : TVar) : Types → Types
  | .atom a => .atom a
  | .atomDual a => .atomDual a
  | .var v => .var (openTVar k u v)
  | .varDual v => .varDual (openTVar k u v)
  | .one => .one
  | .bot => .bot
  | .tensor A B => .tensor (openType k u A) (openType k u B)
  | .parr A B => .parr (openType k u A) (openType k u B)
  | .oplus A B => .oplus (openType k u A) (openType k u B)
  | .amp A B => .amp (openType k u A) (openType k u B)
  | .bang A => .bang (openType k u A)
  | .quest A => .quest (openType k u A)
  | .forall_ A => .forall_ (openType (k+1) u A)
  | .exists_ A => .exists_ (openType (k+1) u A)

def openType0 (u : TVar) (A : Types) : Types :=
  openType 0 u A

def lcTVar : Nat → TVar → Prop
  | _, .free _ => True
  | k, .bound i => i < k

def lcType : Nat → Types → Prop
  | _, .atom _      => True
  | _, .atomDual _  => True
  | k, .var v       => lcTVar k v
  | k, .varDual v   => lcTVar k v
  | _, .one         => true
  | _, .bot         => true
  | k, .tensor A B  => lcType k A ∧ lcType k B
  | k, .parr A B    => lcType k A ∧ lcType k B
  | k, .oplus A B   => lcType k A ∧ lcType k B
  | k, .amp A B     => lcType k A ∧ lcType k B
  | k, .bang A => lcType k A
  | k, .quest A => lcType k A
  | k, .forall_ A => lcType (k+1) A
  | k, .exists_ A => lcType (k+1) A

def lcType0 : Types → Prop := lcType 0

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
