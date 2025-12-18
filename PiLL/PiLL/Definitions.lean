----------------------------------------- IMPORTS -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Lean.PrettyPrinter.Delaborator
import Mathlib.Tactic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Union

------------------------------ POLYMORPHIC CLASSES (NOTATION)------------------------------

class HasSubst (Target New Old : Type) where
  subst : Target → New → Old → Target

notation:max Target "{" New " // " Old "}" => HasSubst.subst Target New Old

class HasBracket (Subject Content Result : Type) where
   brack : Subject → Content → Result

class HasParen (Subject Content Result : Type) where
   paren : Subject → Content → Result

------------------------------- ADDITIONAL FINSET THEOREMS --------------------------------

theorem Finset.biUnion_union {α β : Type _} [DecidableEq α] [DecidableEq β]
  (s t : Finset α) (f : α → Finset β) :
  (s ∪ t).biUnion f = s.biUnion f ∪ t.biUnion f := by
  ext b
  simp [Finset.mem_union]
  constructor
  · rintro  ⟨a, h, hb⟩
    cases h
    · rename_i ha
      left ; exact ⟨a, ha, hb⟩
    rename_i ha
    · right ; exact ⟨a, ha, hb⟩
  · intro h
    cases h
    · rename_i h'
      rcases h' with ⟨a, ha, hb⟩
      exact ⟨a, Or.inl ha, hb⟩
    · rename_i h'
      rcases h' with ⟨a, ha, hb⟩
      exact ⟨a, Or.inr ha, hb⟩

------------------------------------------ TYPES ------------------------------------------

abbrev Atom := Nat

structure TVar where
  name : Nat
deriving Repr, DecidableEq, BEq

instance : ToString TVar where
  toString t := reprStr t

-- FIXME: Probably don't need zero or top
inductive Types : Type where
  | atom      (a : Atom)                -- named type, like A, B, ...
  | atomDual  (a : Atom)                -- dual of a named type
  | var       (v : TVar)                -- type variable
  | varDual   (v : TVar)                -- dual type variables
  | one                                 -- 𝟙 (empty output, unit for ⨂)
  | bot                                 -- ⊥ (empty send, unit for ⅋)
  | zero                                -- 𝟘 (unit for ⊕)
  | top                                 -- ⊤ (unit for &)
  | tensor    (A B : Types)             -- A ⨂ B (send)
  | parr      (A B : Types)             -- A ⅋ B (receive)
  | oplus     (A B : Types)             -- A ⊕ B (select A or B)
  | amp       (A B : Types)             -- A & B (Offer A or B)
  | bang      (A : Types)               -- !A (server accept)
  | quest     (A : Types)               -- ?A (client request)
  | forall_   (v : TVar) (A : Types)    -- ∀X.A (universal type input)
  | exist_    (v : TVar) (A : Types)    -- ∃X.A (existential type output)
deriving DecidableEq, BEq

infixr:90 " ⨂ " => Types.tensor
infixr:90 " ⊕ " => Types.oplus
infixr:90 " ⅋ " => Types.parr
infixr:90 " & " => Types.amp

instance : Zero Types := ⟨Types.zero⟩
instance : One Types := ⟨Types.one⟩
instance : Top Types := ⟨Types.top⟩
instance : Bot Types := ⟨Types.bot⟩

prefix:95 "??" => Types.quest
prefix:95 "!!" => Types.bang

-- FIXME: Needs to bind tighter to the first type after "․" s.t. ∀X.A ⨂ A => (∀X.A) ⨂ A
notation:max "∃" v "․" A => Types.exist_ v A
notation:max "∀" v "․" A => Types.forall_ v A

private def reprTypesAux : Types → Nat → String
  | .atom a, _ => s!"A{a}"
  | .atomDual a, _ => s!"A{a}ᗮ"
  | .var v, _ => s!"V{v}"
  | .varDual v, _ => s!"V{v}ᗮ"
  | .one, _ => "1"
  | .bot, _ => "⊥"
  | .zero, _ => "0" -- FIXME: Probably don't need
  | .top, _ => "⊤"  -- FIXME: Probably don't need
  | .tensor A B, _ => s!"({reprTypesAux A 0} ⨂ {reprTypesAux B 0})"
  | .parr A B, _ => s!"({reprTypesAux A 0} ⅋ {reprTypesAux B 0})"
  | .oplus A B, _ => s!"({reprTypesAux A 0} ⊕ {reprTypesAux B 0})"
  | .amp A B, _ => s!"({reprTypesAux A 0} & {reprTypesAux B 0})"
  | .bang A, _ => s!"!!{reprTypesAux A 0}"
  | .quest A, _ => s!"??{reprTypesAux A 0}"
  | .forall_ v A, _ => s!"∀{v}:{reprTypesAux A 0}"
  | .exist_ v A, _ => s!"∃{v}:{reprTypesAux A 0}"

instance : Repr Types where
  reprPrec A _ := reprTypesAux A 0

instance : ToString Types where
  toString t := reprStr t

def Types.pos : Types → Prop
  | .atom _ => True
  | .var _ => True
  | .one => True
  | .zero => True
  | .tensor _ _ => True
  | .oplus _ _ => True
  | .bang _ => True
  | .exist_ _ _ => True
  | _ => False

def Types.neg : Types → Prop
  | .atomDual _ => True
  | .varDual _ => True
  | .bot => True
  | .top => True
  | .parr _ _ => True
  | .amp _ _ => True
  | .quest _ => True
  | .forall_ _ _ => True
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
  | .zero         => .top
  | .top          => .zero
  | .tensor A B   => .parr (dual A) (dual B)
  | .parr A B     => .tensor (dual A) (dual B)
  | .oplus A B    => .amp (dual A) (dual B)
  | .amp A B      => .oplus (dual A) (dual B)
  | .bang A       => .quest (dual A)
  | .quest A      => .bang (dual A)
  | .forall_ v A  => .exist_ v (dual A)
  | .exist_ v A   => .forall_ v (dual A)

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
  | .atom _ | .atomDual _ | .one | .bot | .zero | .top => ∅
  | .var v        => {v}
  | .varDual v    => {v}
  | .tensor A B   => A.freeTypes ∪ B.freeTypes
  | .parr A B     => A.freeTypes ∪ B.freeTypes
  | .oplus A B    => A.freeTypes ∪ B.freeTypes
  | .amp A B      => A.freeTypes ∪ B.freeTypes
  | .bang A       => A.freeTypes
  | .quest A      => A.freeTypes
  | .forall_ v A  => A.freeTypes \ {v}
  | .exist_ v A   => A.freeTypes \ {v}

-- FIXME: Should aviod capture
def Types.subst (T R : Types) (X : TVar) : Types :=
  match T with
  | .atom a => .atom a
  | .atomDual a => .atomDual a
  | .var v => if v = X then R else .var v
  | .varDual v => if v = X then Rᗮ else .varDual v
  | .one => .one
  | .bot => .bot
  | .zero => .zero  -- FIXME: type probably not needed
  | .top => .top    -- FIXME: type probably not needed
  | .tensor A B => .tensor (A.subst R X) (B.subst R X)
  | .parr A B => .parr (A.subst R X) (B.subst R X)
  | .oplus A B => .oplus (A.subst R X) (B.subst R X)
  | .amp A B => .amp (A.subst R X) (B.subst R X)
  | .bang A => .bang (A.subst R X)
  | .quest A => .quest (A.subst R X)
  | .forall_ v A => if v = X then .forall_ v A else .forall_ v (A.subst R X)
  | .exist_ v A => if v = X then .exist_ v A else .exist_ v (A.subst R X)

instance : HasSubst Types Types TVar where subst := Types.subst

@[simp]
lemma Types.subst_dual (A B : Types) (X : TVar) : Bᗮ{A // X} = B{A // X}ᗮ := by
  induction B <;> simp [dual, HasSubst.subst, subst] <;> try split
  all_goals try simp_all [dual, HasSubst.subst, dual_involution]

def Types.isServerUsable : Types → Prop
  | .quest _  => True
  | .bang _   => True
  | _         => False

------------------------------------------ Proc  ------------------------------------------

abbrev PName := Nat -- Process names are just numbers (ensures not empty)

inductive Proc : Type where
  | tensor    (x y : PName) (P : Proc)            -- x[y].P
  | parr      (x y : PName) (P : Proc)            -- x(y).P
  | one       (x : PName) (P : Proc)              -- x[].P
  | bot       (x : PName) (P : Proc)              -- x().P
  | cut       (x y : PName) (P : Proc)            -- 𝒗xy P
  | par       (P Q : Proc)                        -- P | Q
  | nil                                           -- 𝟘
  | selectL   (x : PName) (P : Proc)              -- x[L].P
  | selectR   (x : PName) (P : Proc)              -- x[R].P
  | amp       (x : PName) (P Q : Proc)            -- x.case{L : P, R : Q}
  | output    (x : PName) (P : Proc) (A : Types)  -- x[A].P
  | input     (x : PName) (P : Proc) (X : TVar)   -- x(X).P
  | server    (x : PName) (P : Proc)              -- !x.{P}
  | consume   (x : PName) (P : Proc)              -- x[USE].P
  | duplicate (x y : PName) (P : Proc)            -- x[DUP](y).P
  | dispose   (x : PName) (P : Proc)              -- x[DISP].P
  | link      (x y : PName)                       -- x ⟷ y
deriving DecidableEq

notation:80 x "⟦⟧․" P => (HasBracket.brack x () : Proc → Proc) P
notation:80 x "⟦"y"⟧․" P => (HasBracket.brack x y : Proc → Proc) P

instance : HasBracket PName Unit (Proc → Proc) where
  brack x _ P := Proc.one x P
instance : HasBracket PName PName (Proc → Proc) where
  brack x y := Proc.tensor x y
instance : HasBracket PName Types (Proc → Proc) where
  brack x T P := Proc.output x P T

notation:80 x "⸨⸩․" P => (HasParen.paren x () : Proc → Proc) P
notation:80 x "⸨"y"⸩․" P => (HasParen.paren x y : Proc → Proc) P

instance : HasParen PName Unit (Proc → Proc) where
  paren x _ P := Proc.bot x P
instance : HasParen PName PName (Proc → Proc) where
  paren := Proc.parr
instance : HasParen PName TVar (Proc → Proc) where
  paren x T P := Proc.input x P T

notation:75 "𝑣" "⸨" x ", " y "⸩ " P:80 => Proc.cut x y P
notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
notation:80 x "⟦DUP⟧⸨" y "⸩․" P:80 => Proc.duplicate x y P
notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
notation:80 "!" x "․{" P:80 "}" => Proc.server x P
notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

notation:80 x "⟷ₚ" y => Proc.link x y
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil

private def reprProcAux : Proc → Nat → String
  | .nil, _ => "𝟘"
  | .tensor x y P, _ => s!"{x}⟦{y}⟧.{reprProcAux P 0}"
  | .one x P, _ => s!"{x}⟦⟧.{reprProcAux P 0}"
  | .parr x y P, _ => s!"{x}⸨{y}⸩.{reprProcAux P 0}"
  | .bot x P, _ => s!"{x}⸨⸩.{reprProcAux P 0}"
  | .cut x y P, _ => s!"𝑣⸨{x}, {y}⸩ {reprProcAux P 0}"
  | .par P Q, _ => s!"({reprProcAux P 0} |ₚ {reprProcAux Q 0})"
  | .selectL x P, _ => s!"{x}⟦𝐋⟧.{reprProcAux P 0}"
  | .selectR x P, _ => s!"{x}⟦𝐑⟧.{reprProcAux P 0}"
  | .amp x P Q, _ =>
      s!"{x}:case" ++ "{" ++ s!" 𝐋 : {reprProcAux P 0}, 𝐑 : {reprProcAux Q 0}" ++ "}"
  | .output x P A, _ => s!"{x}⟦{A}⟧.{reprProcAux P 0}"
  | .input x P X, _ => s!"{x}⟦{X}⟧.{reprProcAux P 0}"
  | .server x P, _ => s!"!{x}:" ++ "{" ++ s!"{reprProcAux P 0}" ++ "}"
  | .consume x P, _ => s!"{x}⟦USE⟧.{reprProcAux P 0}"
  | .duplicate x y P, _ => s!"{x}⟦DUP⟧⸨{y}⸩.{reprProcAux P 0}"
  | .dispose x P, _ => s!"{x}⟦DISP⟧.{reprProcAux P 0}"
  | .link x y, _ => s!"{x}⟷{y}"

instance : Repr Proc where
  reprPrec P _ := reprProcAux P 0

instance : ToString Proc where
  toString p := reprStr p

@[simp]
def Proc.f : Proc → Finset PName
  | .tensor x y P         => {x} ∪ (P.f \ {y})
  | .parr x y P           => {x} ∪ (P.f \ {y})
  | .one x P              => {x} ∪ P.f
  | .bot x P              => {x} ∪ P.f
  | .cut x y P            => P.f \ {x, y}
  | .par P Q              => P.f ∪ Q.f
  | .nil                  => {}
  | .selectL x P          => {x} ∪ P.f
  | .selectR x P          => {x} ∪ P.f
  | .amp x P Q          => {x} ∪ (P.f ∪ Q.f)
  | .output x P _         => {x} ∪ P.f
  | .input  x P _         => {x} ∪ P.f
  | .server x P           => {x} ∪ P.f
  | .consume x P          => {x} ∪ P.f
  | .duplicate x y P      => {x} ∪ (P.f \ {y})
  | .dispose x P          => {x} ∪ P.f
  | .link x y             => {x, y}

@[simp]
def Proc.names : Proc → Finset PName
  | .tensor x y P         => {x, y} ∪ P.names
  | .parr x y P           => {x, y} ∪ P.names
  | .one x P              => {x} ∪ P.names
  | .bot x P              => {x} ∪ P.names
  | .cut x y P            => {x, y} ∪ P.names
  | .par P Q              => P.names ∪ Q.names
  | .nil                  => {}
  | .selectL x P          => {x} ∪ P.names
  | .selectR x P          => {x} ∪ P.names
  | .amp x P Q          => {x} ∪ (P.names ∪ Q.names)
  | .output x P _         => {x} ∪ P.names
  | .input  x P _         => {x} ∪ P.names
  | .server x P           => {x} ∪ P.names
  | .consume x P          => {x} ∪ P.names
  | .duplicate x y P      => {x, y} ∪ P.names
  | .dispose x P          => {x} ∪ P.names
  | .link x y             => {x, y}

def Proc.boundNames (P : Proc) : Finset PName :=
  P.names \ P.f

abbrev Renaming := PName → PName

def rename (ρ : Renaming) : Proc → Proc
  | .tensor x y P     => .tensor (ρ x) (ρ y) (rename ρ P)
  | .parr x y P       => .parr (ρ x) (ρ y) (rename ρ P)
  | .one x P          => .one (ρ x) (rename ρ P)
  | .bot x P          => .bot (ρ x) (rename ρ P)
  | .cut x y P        => .cut (ρ x) (ρ y) (rename ρ P)
  | .par P Q          => .par (rename ρ P) (rename ρ Q)
  | .nil              => .nil
  | .selectL x P      => .selectL (ρ x) (rename ρ P)
  | .selectR x P      => .selectR (ρ x) (rename ρ P)
  | .amp x P Q      => .amp (ρ x) (rename ρ P) (rename ρ Q)
  | .output x P A     => .output (ρ x) (rename ρ P) A
  | .input x P A      => .input (ρ x) (rename ρ P) A
  | .server x P       => .server (ρ x) (rename ρ P)
  | .consume x P      => .consume (ρ x) (rename ρ P)
  | .duplicate x y P  => .duplicate (ρ x) (ρ y) (rename ρ P)
  | .dispose x P      => .dispose (ρ x) (rename ρ P)
  | .link x y         => .link (ρ x) (ρ y)

def freshName (s : Finset Nat) : PName :=
  (Finset.fold Nat.max 0 id s) + 1

def renameBound old new P := rename (fun curr => if curr = old then new else curr) P

def renameBound2 old1 old2 new1 new2 P := renameBound old2 new2 (renameBound old1 new1 P)

-- Only bound names should be renamed and free names should match exactly
inductive AlphaEq : Proc → Proc → Prop where
  | nil : AlphaEq .nil .nil

  | par {P1 Q1 P2 Q2 : Proc} :
      AlphaEq P1 Q1 → AlphaEq P2 Q2 → AlphaEq (.par P1 P2) (.par Q1 Q2)

  | one {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.one x P) (.one x' Q)

  | tensor {P Q : Proc} {x y x' y' : PName} -- x, x' are free y, y' are bound
      (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
      AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
      AlphaEq (.tensor x y P) (.tensor x' y' Q)

  | bot {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.bot x P) (.bot x' Q)

  | parr {P Q : Proc} {x y x' y' : PName} -- x x' are Free, y y' are bound
      (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
        AlphaEq (.parr x y P) (.parr x' y' Q)

  | cut {P Q : Proc} {x y x' y' : PName} -- x y x' y' are all bound
      (w1 w2 : PName) (hFresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ Q.names ∧ w2 ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound2 x y w1 w2 P) (renameBound2 x' y' w1 w2 Q) →
        AlphaEq (.cut x y P) (.cut x' y' Q)

  | selectL {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.selectL x P) (.selectL x' Q)

  | selectR {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.selectR x P) (.selectR x' Q)

  | amp {P1 Q1 P2 Q2 : Proc} {x x' : PName} :
      AlphaEq P1 P2 → AlphaEq Q1 Q2 → x = x' → AlphaEq (.amp x P1 Q1) (.amp x' P2 Q2)

  | output {P Q : Proc} {x x' : PName} {A A' : Types}:
      AlphaEq P Q → x = x' → A = A' → AlphaEq (.output x P A) (.output x' Q A')

  | input {P Q : Proc} {x x' : PName} {X X' : TVar} :
      AlphaEq P Q → x = x' → X = X' → AlphaEq (.input x P X) (.input x' Q X')

  | server {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.server x P) (.server x' Q)

  | consume {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.consume x P) (.consume x' Q)

  | duplicate {P Q : Proc} {x y x' y' : PName} :
      AlphaEq P Q → x = x' → y = y' → AlphaEq (.duplicate x y P) (.duplicate x' y' Q)

  | dispose {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.dispose x P) (.dispose x' Q)

  | link {x y x' y' : PName} :
      x = x' → y = y' → AlphaEq (.link x y) (.link x' y')

notation:60 P " =ₐ " Q => AlphaEq P Q

@[simp]
def Proc.size : Proc → Nat
| .nil => 1
| .link _ _ => 1
| .par P Q => 1 + P.size + Q.size
| .amp _ P Q => 1 + P.size + Q.size
| .tensor _ _ P | .parr _ _ P | .one _ P | .bot _ P | .cut _ _ P | .selectL _ P
| .selectR _ P | .output _ P _ | .input _ P _ | .server _ P | .consume _ P
| .dispose _ P | .duplicate _ _ P => 1 + P.size

lemma freshName_is_fresh (s : Finset PName) : freshName s ∉ s := by
  let m := Finset.fold Nat.max 0 id s
  have h_max : ∀ n ∈ s, n ≤ m := by
    intro n hn ; rw [Finset.le_fold_max] ; grind
  intro h_contra
  specialize h_max (freshName s) h_contra
  unfold m freshName at h_max
  apply Nat.not_succ_le_self (Finset.fold Nat.max 0 id s)
  exact h_max

lemma size_renameBound_eq (old new : PName) (P : Proc) :
  (renameBound old new P).size = P.size := by
  induction P
  case nil | link =>
    simp [renameBound, Proc.size]
    apply rfl
  case one P ih | bot P ih | selectL P ih | selectR P ih | server P ih
    | consume P ih | duplicate P ih | dispose P ih =>
    simp [renameBound, rename, Proc.size]
    unfold renameBound at ih
    apply ih
  case input P A ih | output P X ih | tensor P ih | parr P ih | cut P ih =>
    simp [renameBound, rename, Proc.size]
    simp [renameBound] at ih
    rw [ih]
  case par P Q ihP ihQ | amp P Q ihP ihQ =>
    simp [renameBound, rename, Proc.size]
    simp [renameBound] at ihP
    simp [renameBound] at ihQ
    rw [ihP, ihQ]

@[refl]
theorem AlphaEq.refl (P : Proc) : P =ₐ P := by
  induction h : P.size using Nat.strong_induction_on generalizing P
  rename_i n ih
  cases P

  case nil | link => repeat constructor

  case par P Q =>
    constructor
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
        omega
      · rfl
    · apply ih Q.size
      · rw [← h]
        simp [Proc.size]
      · rfl

  case tensor x y P | parr x y P =>
    constructor
    · simp ; exact freshName_is_fresh P.names
    · apply ih P.size
      · rw [← h]
        simp only [Proc.size]
        omega
      · simp [size_renameBound_eq]
    · rfl

  case cut x y P =>
    let w1 := freshName P.names
    let w2 := freshName (P.names ∪ {w1})
    have h_fresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ P.names ∧ w2 ∉ P.names ∪ P.names := by
      constructor
      · intro h_eq ; unfold w1 at h_eq ; unfold w2 at h_eq
        exact absurd (freshName_is_fresh (P.names ∪ {w1})) (by grind)
      · simp
        apply And.intro
        · exact freshName_is_fresh P.names
        · unfold w2 w1
          · intro h_contra
            apply freshName_is_fresh (P.names ∪ {freshName P.names})
            apply Finset.mem_union_left
            exact h_contra
    apply AlphaEq.cut
    · exact h_fresh
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
      · unfold renameBound2
        simp [size_renameBound_eq]

  case one _ P | bot _ P | selectL _ P | selectR _ P | server _ P | dispose _ P
    | consume _ P | duplicate _ _ P | output _ P _ | input _ P _ =>
    constructor
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
      · rfl
    repeat rfl

  case amp _ P Q =>
    apply AlphaEq.amp
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
        omega
      · rfl
    · apply ih Q.size
      · rw [← h]
        simp [Proc.size]
      · rfl
    · rfl

lemma AlphaEq.symm (P Q : Proc) (h : P =ₐ Q) : (Q =ₐ P) := by
  induction h
  case nil => rfl
  case one | bot | par | selectL | selectR | amp | output | input | server
    | consume | duplicate | dispose | link => constructor ; repeat simp [*]

  case tensor _ _ _ _ _ _ _ hwnPQ _ hxxp hrbQP
    | parr tensor _ _ _ _ _ _ hwnPQ _ hxxp hrbQP =>
    constructor
    · rw [Finset.union_comm] ; exact hwnPQ
    · exact hrbQP
    · rw [Eq.comm] ; exact hxxp

  case cut _ _ _ _ _ _ _ _ h_fresh hrbPQ hrbQP =>
    constructor
    · rw [Finset.union_comm] ; exact h_fresh
    · exact hrbQP

theorem AlphaEq.comm (P Q : Proc) : (P =ₐ Q) = (Q =ₐ P) := by
  apply propext
  constructor
  · apply AlphaEq.symm
  · apply AlphaEq.symm

-- lemma renameBound_comm {x y a b : PName} {P : Proc} :
--   (hxy : x ≠ y) → (hab : a ≠ b) → (hxb : x ≠ b) → (hya : y ≠ a) →
--   renameBound x a (renameBound y b P) = renameBound y b (renameBound x a P) := by
--   intros
--   induction P <;> simp [renameBound, rename, *]
--   case one ih | bot ih | selectL ih | selectR ih | output ih | input ih
--     | server ih | consume ih | dispose ih =>
--     apply And.intro
--     · aesop
--     · exact ih

--   case par P_ih Q_ih =>
--     apply And.intro
--     · exact P_ih
--     · exact Q_ih

--   case amp P_ih Q_ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · exact P_ih
--       · exact Q_ih

--   case link =>
--     apply And.intro
--     · aesop
--     · aesop

--   case tensor ih | parr ih | cut ih | duplicate ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · aesop
--       · exact ih

-- lemma renameBound_commutes (a b : PName) (P : Proc) (ha : a ∉ P.names) (hb : b ∉ P.names) :
--   renameBound a b P = P := by
--   induction P generalizing a b
--   all_goals simp [rename, renameBound, *]

--   case tensor x y P ih | parr x y P ih | cut x y P ih | duplicate x y P ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · intro h ; simp_all
--       · apply ih <;> simp_all

--   case one x P ih | bot x P ih | selectL x P ih | selectR x P ih | server x P ih
--     | consume x P ih | dispose x P ih | output x P A ih | input x P X ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply ih <;> simp_all

--   case amp x P Q ihP ihQ =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · apply ihP <;> simp_all
--       · apply ihQ <;> simp_all

--   case par P Q ihP ihQ =>
--     apply And.intro
--     · apply ihP <;> simp_all
--     · apply ihQ <;> simp_all

--   case link =>
--     apply And.intro
--     · intro h ; simp_all
--     · intro h ; simp_all


-- lemma renameBound_comp (x y z : PName) (P : Proc) (hx : x ∉ P.names) (hxy : x ≠ y) :
--   renameBound x z (renameBound y x P) = renameBound y z P := by
--   induction P generalizing x y z <;> simp [renameBound, rename, *] at *
--   all_goals aesop

-- lemma AlphaEq_swap_fresh (y y' w1 w2 : PName) (P Q : Proc)
--   (hFresh1 : w1 ∉ P.names ∪ Q.names)
--   (hFresh2 : w2 ∉ P.names ∪ Q.names)
--   (h : renameBound y w1 P =ₐ renameBound y' w1 Q) :
--   (renameBound y w2 P =ₐ renameBound y' w2 Q) := by sorry

theorem AlphaEq.trans (P Q R : Proc) (hPQ : P =ₐ Q) (hQR : Q =ₐ R) : P =ₐ R := by sorry
--   induction P.size + Q.size using Nat.strong_induction_on generalizing P Q R
--   rename_i n ih
--   cases hPQ <;> cases hQR
--   case nil.nil => rfl
--   case par.par =>
--     rename_i P1 Q1 P2 Q2 h1 h2 Q1' Q2' h5 h6
--     apply AlphaEq.par
--     · sorry

def Proc.substTypes (P : Proc) (A : Types) (X : TVar) : Proc :=
  match P with
  | .nil => .nil
  | .one x P => .one x (P.substTypes A X)
  | .bot x P => .bot x (P.substTypes A X)
  | .tensor x y P => .tensor x y (P.substTypes A X)
  | .parr x y P => .parr x y (P.substTypes A X)
  | .cut x y P => .cut x y (P.substTypes A X)
  | .par P Q => .par (P.substTypes A X) (Q.substTypes A X)
  | .selectL x P => .selectL x (P.substTypes A X)
  | .selectR x P => .selectR x (P.substTypes A X)
  | .amp x P Q => .amp x (P.substTypes A X) (Q.substTypes A X)
  | .server x P => .server x (P.substTypes A X)
  | .dispose x P => .dispose x (P.substTypes A X)
  | .duplicate x y P => .duplicate x y (P.substTypes A X)
  | .consume x P => .consume x (P.substTypes A X)
  | .link x y => .link x y
  | .output x P B => .output x (P.substTypes A X) (B.subst A X)
  | .input x P Y => if Y = X then .input x P Y else .input x (P.substTypes A X) Y

instance : HasSubst Proc Types TVar where subst := Proc.substTypes

def Proc.substName (P : Proc) (x z : PName) : Proc :=
  let sub := fun (c : PName) => if c = z then x else c
  match P with
  | .nil => .nil
  | .one a P => .one (sub a) (P.substName x z)
  | .bot a P => .bot (sub a) (P.substName x z)
  | .tensor a b P =>
      if b = z then .tensor (sub a) b P
      else .tensor (sub a) b (P.substName x z)
  | .parr a b P =>
      if b = z then .parr (sub a) b P
      else .parr (sub a) b (P.substName x z)
  | .cut a b P =>
      if a = z ∨ b = z then .cut a b P
      else .cut (sub a) (sub b) (P.substName x z)
  | .par P Q => .par (P.substName x z) (Q.substName x z)
  | .selectL a P => .selectL (sub a) (P.substName x z)
  | .selectR a P => .selectR (sub a) (P.substName x z)
  | .amp a P Q => .amp (sub a) (P.substName x z) (Q.substName x z)
  | .server a P => .server (sub a) (P.substName x z)
  | .dispose a P => .dispose (sub a) (P.substName x z)
  | .duplicate a b P =>
      if b = z then .duplicate (sub a) b P
      else .duplicate (sub a) (sub b) (P.substName x z)
  | .consume a P => .consume (sub a) (P.substName x z)
  | .link a b => .link (sub a) (sub b)
  | .output a P A => .output (sub a) (P.substName x z) A
  | .input a P X => .input (sub a) (P.substName x z) X

instance : HasSubst Proc PName PName where subst := Proc.substName

def Proc.close (P : Proc) (names : List PName) : Proc :=
  match P with
  | .server x _ => names.foldr (fun n acc => Proc.dispose n acc) (x⟦⟧․𝟘)
  | _ => P

def Proc.open (P : Proc) (names : List PName) (σ : Renaming) : Proc :=
  match P with
  | .server _ _  => names.foldr (fun n acc => Proc.duplicate n (σ n) acc) ((rename σ P) |ₚ P)
  | _ => P

@[simp]
lemma Proc.substName_par (P Q : Proc) (x z : PName) :
  P{x // z} |ₚ Q{x // z} = (P |ₚ Q){x // z} := by
  dsimp [HasSubst.subst, Proc.substName]

-- FIXME: Not sure how many of these are still used for anything
lemma Proc.boundNames_par_subset_left (P Q : Proc) (x : PName)
  (hxBP : x ∈ P.boundNames) (hNotQf : x ∉ Q.f) :
  x ∈ (P |ₚ Q).boundNames := by
  simp only [Proc.boundNames, Proc.names, Proc.f] at *
  simp at hxBP
  rcases hxBP with ⟨hxP, hxNotPf⟩
  simp
  apply And.intro
  · left ; exact hxP
  · simp [hxNotPf, hNotQf]

lemma Proc.not_bound_par_left {P Q : Proc} {x : PName}
  (hSafe : x ∉ (P |ₚ Q).boundNames) (hNotQf : x ∉ Q.f) :
  x ∉ P.boundNames := by
  intro h_contra
  apply hSafe
  exact Proc.boundNames_par_subset_left P Q x h_contra hNotQf

lemma Proc.not_bound_par_right {P Q : Proc} {x : PName}
  (hSafe : x ∉ (P |ₚ Q).boundNames) (hxNotPf : x ∉ P.f) :
  x ∉ Q.boundNames := by
  intro h_contra
  apply hSafe
  simp only [Proc.boundNames, Proc.names, Proc.f] at *
  simp at h_contra
  rcases h_contra with ⟨hxQ, hxNotQf⟩
  simp
  apply And.intro
  · right ; exact hxQ
  · simp [hxNotPf, hxNotQf]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env := Finset (PName × Types)

abbrev EmptyEnv : Env := ∅

/- FIXME: eval does not work since non-computable -/
-- noncomputable instance : Repr Env where
--   reprPrec (Γ : Env) _ :=
--     if Γ = ∅ then "∅"
--     else
--       let entries := Γ.toList.map (fun (x, A) => s!"{x} ∶ {reprStr A}")
--       String.intercalate "‚ " entries

-- noncomputable instance : ToString Env where
--   toString e := reprStr e

def Env.mk (x : PName) (A : Types) : Env := {(x, A)}
infixr:86 " ∶ " => Env.mk

-- NOTE: It's a set so linear by definition
-- def Env.linear (Δ : Env) : Prop :=
  -- (Δ.image Prod.fst).card = Δ.card

@[simp]
def Env.names (Δ : Env) : Finset (PName) :=
  (Δ.image Prod.fst)

@[simp]
def Env.disjoint (Δ Γ : Env) : Prop :=
  Δ.names ∩ Γ.names = ∅

noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
  -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

notation Δ "⸨" x "⸩ₑ" => Env.lookup Δ x

-- Order independent equality for environments
@[simp]
def Env.Eq (Δ Γ : Env) : Prop :=
  ∀ x : (PName), Δ⸨x⸩ₑ = Γ⸨x⸩ₑ

notation Δ " =ₑ " Γ => Env.Eq Δ Γ

-- Eq reflexivity
@[simp]
theorem Env.Eq_refl (Δ : Env) : Δ =ₑ Δ :=
  fun _ => rfl

-- Eq symmetry
theorem Env.Eq_symm (Δ Γ : Env) (h : Δ =ₑ Γ) : Γ =ₑ Δ :=
  fun x => (h x).symm

-- Eq transitivity
theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Δ =ₑ Γ) (h₂ : Γ =ₑ Ε) : Δ =ₑ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence Env.Eq :=
⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

infixl:85 "‚ " => Env.merge

-- Merge identity
@[simp]
theorem Env.merge_unitR (Δ : Env) : Δ‚ ∅ = Δ := by
  simp [Env.merge]

@[simp]
theorem Env.merge_unitL (Δ : Env) : ∅‚ Δ = Δ := by
  simp [Env.merge]


-- Merge commutivity
theorem Env.merge_comm (Δ Γ : Env) : Δ‚ Γ = Γ‚ Δ := by
  simp [Env.merge, Finset.union_comm]

-- Merge associativity
theorem Env.merge_assoc (Δ Γ Ε : Env) : Δ‚ Γ‚ Ε = Δ‚ (Γ‚ Ε) := by
  simp [Env.merge]

lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
  (Γ‚ Δ)‚ Ξ = (Γ‚ Ξ)‚ Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]

lemma Env.merge_move_last_two_left (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ε‚ Δ‚ Ξ := by
  rw [Env.merge_swap_last, Env.merge_swap_last Γ Δ Ε]

lemma Env.merge_move_second_two_right (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ξ‚ Ε‚ Δ := by
  rw [Env.merge_swap_last Γ Δ Ξ, Env.merge_swap_last]

@[simp]
def Env.serverUsable (Γ : Env) : Prop :=
  ∀p, p ∈ Γ → (p.snd).isServerUsable = True

prefix:max "?ₑ" => Env.serverUsable

@[simp]
def Env.freeTypes (Γ : Env) : Finset TVar :=
  Γ.biUnion (fun (_, A) => A.freeTypes)

notation "ft(" Γ ")" => Env.freeTypes Γ

def Env.substName (Γ : Env) (x z : PName) : Env :=
  Γ.image (fun (n, T) => if n = z then (x, T) else (n, T))

instance : HasSubst Env PName PName where subst := Env.substName

def Env.substTypes (Γ : Env) (A : Types) (X : TVar) : Env :=
  Γ.image (fun (n, T) => (n, T.subst A X))

instance : HasSubst Env Types TVar where subst := Env.substTypes

@[simp]
lemma Env.serverUsable_subst (Γ : Env) (x z : PName) (h : ?ₑΓ) :
  ?ₑ(Γ{x // z}) := by
  simp only [Env.serverUsable, HasSubst.subst, Env.substName] at *
  simp only [Finset.forall_mem_image, apply_ite] at *
  simp at *
  exact h

lemma Env.names_substName (Γ : Env) (x z : PName) :
  Γ{x // z}.names = Γ.names.image (fun n => if n = z then x else n) := by
  simp only [Env.names, HasSubst.subst, Env.substName, Finset.image_image]
  apply Finset.image_congr
  intro ⟨n, t⟩ _
  dsimp
  split_ifs <;> rfl

@[simp]
lemma Env.substName_eq_self_of_not_mem (Γ : Env) (x z : PName)
  (h : z ∉ Γ.names) : Γ{x // z} = Γ := by
  simp only [HasSubst.subst, Env.substName]
  conv_rhs => rw [← Finset.image_id (s := Γ)]
  apply Finset.image_congr
  intro p hpΓ
  simp_all
  intro a
  subst a
  simp_all

@[simp] lemma Env.names_mk (x : PName) (A : Types) :
  (x ∶ A).names = {x} := by
  simp [Env.names, Env.mk]

@[simp] lemma Env.merge_mk_left (x : PName) (A : Types) (Γ : Env) :
  (x ∶ A)‚ Γ = {(x, A)} ∪ Γ := rfl

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := ∅

instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

/- FIXME: eval does not work since non-computable -/
-- open Lean in
-- noncomputable instance : Repr HyperEnv where
--   reprPrec (𝒢 : HyperEnv) _ :=
--     if 𝒢 = ∅ then "∅"
--     else
--       let entries := 𝒢.toList.map repr
--       Format.joinSep entries " |ₕ "

-- noncomputable instance : ToString HyperEnv where
--   toString g := reprStr g

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

-- FIXME: Relevance?
-- def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
  -- ∀ Δ ∈ 𝒢, Δ.linear ∧                            -- ensure each env is linear
  -- pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

@[simp]
def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
  𝒢.biUnion Env.names

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
  (𝒢.toList.find? (fun Δ => Δ⸨x⸩ₑ ≠ none)) >>= fun Δ  => Δ⸨x⸩ₑ

notation:60 𝒢 "⸨" x "⸩ₕ" => HyperEnv.lookup 𝒢 x

def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar (Linear by definition of Finset)
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  -- 𝒢.linear ∧ ℋ.linear ∧
  -- (𝒢 ∩ ℋ).card = 0 ∧
  -- (𝒢.names ∩ ℋ.names).card = 0
  Disjoint 𝒢.names ℋ.names

-- Order independent equality for hyper-environments
@[simp]
def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
  -- (1) 𝒢 and ℋ must define the same names
  -- (2) The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  ∀ x ∈ HyperEnv.names 𝒢, 𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ

notation 𝒢 " =ₕ " ℋ => HyperEnv.Eq 𝒢 ℋ

-- Eq reflexivity
@[simp]
theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : 𝒢 =ₕ 𝒢 := by
  simp

-- Eq symmetry
theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : 𝒢 =ₕ ℋ) : ℋ =ₕ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- Eq transitivity
theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : 𝒢 =ₕ ℋ) (h₂ : ℋ =ₕ 𝒦) :
  𝒢 =ₕ 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
    calc
      𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ := h₁_vals x hx
      _          = 𝒦⸨x⸩ₕ := h₂_vals x hxH

instance : Equivalence HyperEnv.Eq :=
⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

@[simp]
abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

infixl:55 " |ₕ " => HyperEnv.merge

-- Merge identity
@[simp]
theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

@[simp]
theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

-- Merge commutative
theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : 𝒢 |ₕ ℋ = ℋ |ₕ 𝒢 := by
  simp [Finset.union_comm]

-- Merge associativity
theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) : (𝒢 |ₕ ℋ) |ₕ 𝒦 = 𝒢 |ₕ (ℋ |ₕ 𝒦) := by
  simp

def HyperEnv.substName (𝒢 : HyperEnv) (x z : PName) : HyperEnv :=
  𝒢.image (fun Γ => Γ{x // z})

instance : HasSubst HyperEnv PName PName where subst := HyperEnv.substName

def HyperEnv.substTypes (𝒢 : HyperEnv) (A : Types) (X : TVar) : HyperEnv :=
  𝒢.image (fun Γ => Γ.substTypes A X)

instance : HasSubst HyperEnv Types TVar where subst := HyperEnv.substTypes

@[simp]
lemma HyperEnv.names_merge (𝒢 ℋ : HyperEnv) : (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  simp [Finset.biUnion_union]

lemma HyperEnv.substName_merge (𝒢 ℋ : HyperEnv) (x z : PName) :
  𝒢{x // z} |ₕ ℋ{x // z} = (𝒢 |ₕ ℋ){x // z} := by
  simp [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]

lemma Finset.disjoint_image_substName {α : Type*} [DecidableEq α]
  (s t : Finset α) (x z : α) :
  Disjoint s t → x ∉ s → x ∉ t →
  Disjoint (s.image (fun n => if n = z then x else n))
           (t.image (fun n => if n = z then x else n)) := by
  intro h_disj h_sx h_tx
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  rw [Finset.mem_image] at ha hb
  rcases ha with ⟨a_pre, ha_pre, rfl⟩
  rcases hb with ⟨b_pre, hb_pre, h_eq⟩
  rw [←h_eq]

  split_ifs at * with h_az h_bz
  · rw [h_az] at ha_pre
    rw [h_bz] at hb_pre
    rw [Finset.disjoint_iff_ne] at h_disj
    exfalso
    exact h_disj z ha_pre z hb_pre rfl
  · intro h_contra
    rw [← h_contra] at hb_pre
    contradiction
  · intro h_contra
    rw [h_contra] at ha_pre
    contradiction
  · intro h_contra
    rw [← h_contra] at hb_pre
    rw [Finset.disjoint_iff_ne] at h_disj
    exact h_disj a_pre ha_pre a_pre hb_pre rfl

lemma HyperEnv.names_substName (𝒢 : HyperEnv) (x z : PName) :
  𝒢{x // z}.names = 𝒢.names.image (fun n => if n = z then x else n) := by
  simp only [HyperEnv.names, HasSubst.subst, HyperEnv.substName]
  rw [Finset.biUnion_image]
  rw [Finset.image_biUnion]
  apply Finset.biUnion_congr
  · rfl
  · intro Γ _
    apply Env.names_substName

@[simp]
lemma HyperEnv.substName_preserve_disjoint (𝒢 ℋ : HyperEnv) (x z : PName)
  (hDisj : 𝒢.disjoint ℋ) (hFresh : x ∉ (𝒢 |ₕ ℋ).names) :
  𝒢{x // z}.disjoint ℋ{x // z} := by
  dsimp only [HyperEnv.disjoint]
  rw [HyperEnv.names_merge] at hFresh
  have h_fresh_G : x ∉ 𝒢.names :=
    fun h => hFresh (Finset.mem_union_left _ h)
  have h_fresh_H : x ∉ ℋ.names :=
    fun h => hFresh (Finset.mem_union_right _ h)
  simp only [HyperEnv.names_substName]
  apply Finset.disjoint_image_substName
  · exact hDisj
  · exact h_fresh_G
  · exact h_fresh_H

lemma HyperEnv.substName_eq_self_of_not_mem (𝒢 : HyperEnv) (x z : PName)
  (h : z ∉ 𝒢.names) : 𝒢{x // z} = 𝒢 := by
  simp only [HasSubst.subst, HyperEnv.substName, Env.substName]
  conv_rhs => rw [← Finset.image_id (s := 𝒢)]
  apply Finset.image_congr
  intro Γ hΓ𝒢
  simp
  apply Env.substName_eq_self_of_not_mem
  simp_all

--------------------------------------- TYPING RULES ---------------------------------------

-- FIXME: Added a lot of extra contranints so facilitate Env / HyperEnv disjointness
-- as well as no pathological process appearing e.g. x(x).P, x[DUP](x).P etc.

inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
      ----------
      Typing ∅ 𝟘

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {hDisj : 𝒢.disjoint ℋ}:
      Typing 𝒢 P → Typing ℋ Q →
      --------------------------
      Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types)
      {hFrehs : ∀ s ∈ [x, y], s ∉ (𝒢.names ∪ Γ.names ∪ Δ.names)} -- FIXME: Check if this is correct and sufficient
      {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
      Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
      -------------------------------------
      Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types}
      {hFresh : x ∉ Γ.names ∧ y ∉ Δ.names}
      {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
      -- FIXME: Should it also be check that x ∉ Δ ∧ y ∉ Γ ??
      Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
      ---------------------------------
      Typing (Γ‚ Δ‚ x ∶ A ⨂ B) (x⟦y⟧․P)

  | one {P : Proc} {x : PName} :
      Typing ∅ P →
      ----------------------
      Typing (x ∶ 1) (x⟦⟧․P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types}
      {hFresh : x ∉ Γ.names ∧ y ∉ Γ.names}
      {hneq : x ≠ y} :
      Typing (Γ‚ y ∶ A‚ x ∶ B) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩․P)

  | bot {Γ : Env} {P : Proc} {x : PName} {hFresh : x ∉ Γ.names}
      {hFresh : x ∉ Γ.names} :
      Typing Γ P →
      --------------------------
      Typing (Γ‚ x ∶ ⊥) (x⸨⸩․P)

  | oplus₁
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧․P)

  | oplus₂
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ B) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧․P)

  | amp
      {Γ : Env} {P Q : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P → Typing (Γ‚ x ∶ B) Q →
      ---------------------------------------------
      Typing (Γ‚ x ∶ A & B) (x․case{𝐋 : P, 𝐑 : Q})

  | quest
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P →
      -----------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦USE⟧․P)

  | w
      {Γ : Env} {P : Proc} {x : PName} {A : Types} {hFrehs : x ∉ Γ.names} :
      Typing Γ P →
      -----------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦DISP⟧․P)

  | c -- FIXME: hneq is not in paper rule but here to avoid e.g. x[DUP](x).P, which
      -- breaks resource counting since Finset doesn't allow duplicates
      {Γ : Env} {P : Proc} {x x' : PName} {A : Types} {hneq : x ≠ x'} :
      Typing (Γ‚ x ∶ ??A‚ x' ∶ ??A) P →
      ---------------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦DUP⟧⸨x'⸩․P)

  | bang
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P → ?ₑΓ →
      ------------------------------
      Typing (Γ‚ x ∶ !!A) (!x․{P})

  | exists_
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar} :
      Typing (Γ‚ x ∶ B{A // X}) P →
      -----------------------------
      Typing (Γ‚ x ∶ ∃X․B) (x⟦A⟧․P)

  | forall_
      {Γ : Env} {P : Proc} {x : PName} {B : Types} {X : TVar} :
      Typing (Γ‚ x ∶ B) P → X ∉ ft(Γ) →
      ---------------------------------
      Typing (Γ‚ x ∶ ∀X․B) (x⸨X⸩․P)

  | ax
      {x y : PName} {A : Types} {hneq : x ≠ y} :
      Typing (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₚ y)

notation:50 "⊢ " P " ∷ " T => Typing T P



-- FIXME: Move to Env section
@[simp]
lemma Env.names_singleton (x : PName) (A : Types) :
  (x ∶ A).names = {x} := by
  simp only [Env.names]
  rfl

@[simp]
lemma Env.names_empty : (∅ : Env).names = ∅ := by simp

@[simp] lemma Env.names_distributes (Γ Δ : Env) :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by
    simp only [Env.names, ← Finset.image_union]
    rfl

-- FIXME: Move to HyperEnv section
@[simp]
lemma HyperEnv.names_singleton (x : PName) (A : Types) :
  ({(x ∶ A)} : HyperEnv).names = {x} := by
  simp only [HyperEnv.names, Finset.singleton_biUnion]
  rfl

@[simp]
lemma HyperEnv.names_distributes (Γ : Env) :
  ({Γ} : HyperEnv).names = Γ.names := by
  simp [HyperEnv.names, Env.names, Finset.singleton_biUnion]

@[simp]
lemma HyperEnv.names_empty : (∅ : HyperEnv).names = ∅ := by simp



lemma Typing.Pf_subset_HyperEnvNames {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
  P.f ⊆ 𝒢.names := by
  induction h

  case mix₀ =>
    simp only [Proc.f, HyperEnv.names_empty, subset_refl]

  case mix ihP ihQ =>
    simp [Finset.biUnion_union]
    exact Finset.union_subset_union ihP ihQ

  case one | bot | w =>
    simp only [Proc.f, HyperEnv.names_distributes,
      Env.names_distributes, Env.names_singleton]
    simp_all

  case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
    simp only [Proc.f, HyperEnv.names_distributes, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.insert_subset
    · simp
    · exact ih

  case amp ihP ihQ =>
    simp only [Proc.f, HyperEnv.names_distributes, Env.names_distributes,
      Env.names_singleton] at *
    · apply Finset.insert_subset
      · simp
      · exact Finset.union_subset ihP ihQ

  case c ih =>
    simp only [Proc.f, HyperEnv.names_distributes, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.insert_subset
    · simp
    · intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
      specialize ih ha.1
      simp_all

  case ax =>
    simp only [Proc.f, HyperEnv.names_distributes, Env.names_distributes,
      Env.names_singleton, Finset.union_singleton]
    simp [Finset.pair_comm]

  case cut ih =>
    simp only [Proc.f, HyperEnv.names_merge, HyperEnv.names_distributes,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    rw [Finset.mem_sdiff] at ha
    specialize ih ha.1
    simp_all

  case tensor ih | parr ih =>
    simp only [Proc.f, HyperEnv.names_merge, HyperEnv.names_distributes,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    simp at ⊢ ha ih
    rcases ha with rfl | ⟨hP, hny⟩
    · left ; rfl
    · specialize ih hP ; simp at ih ; tauto




@[simp] lemma Env.substName_empty (x z : PName) :
  (∅ : Env){x // z} = ∅ := by
  simp only [HasSubst.subst, Env.substName, Finset.image_empty]

@[simp] lemma Env.substName_distributes (Γ Δ : Env) (x z : PName) :
  (Γ‚ Δ){x // z} = Γ{x // z}‚ Δ{x // z} := by
  simp [HasSubst.subst, Env.substName, Env.merge, Finset.image_union]

@[simp] lemma Env.substName_singleton (x y z : PName) (A : Types) :
  (y ∶ A){x // z} = (if y = z then x else y) ∶ A := by
  simp only [HasSubst.subst, Env.substName, Env.mk, Finset.image_singleton]
  split <;> rfl



@[simp] lemma HyperEnv.substName_empty (x z : PName) :
  (∅ : HyperEnv){x // z} = ∅ := by
  simp only [HasSubst.subst, HyperEnv.substName, Finset.image_empty]

@[simp] lemma HyperEnv.substName_singleton (Γ : Env) (x z : PName) :
  ({Γ} : HyperEnv){x // z} = Γ{x // z} := by
  simp only [HasSubst.subst, HyperEnv.substName, Finset.image_singleton]

@[simp] lemma HyperEnv.substName_distributes (𝒢 ℋ : HyperEnv) (x z : PName) :
  (𝒢 |ₕ ℋ){x // z} = 𝒢{x // z} |ₕ ℋ{x // z} := by
  simp only [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]




@[simp] lemma Proc.substname_nil (x z : PName) :
  𝟘{x // z} = 𝟘 := by simp only [HasSubst.subst, Proc.substName]

@[simp] lemma Proc.substName_link (a b x z : PName) :
  (a⟷ₚb){x // z} = (if a = z then x else a)⟷ₚ(if b = z then x else b) := by
  simp only [HasSubst.subst, Proc.substName]

@[simp] lemma Proc.boundNames_one (x : PName) (P : Proc) (h : x ∉ P.boundNames) :
  ((x⟦⟧․P).boundNames) = ((x⟦⟧․𝟘).boundNames ∪ P.boundNames) := by
  simp [Proc.boundNames, Proc.names, Proc.f, Finset.empty_union] at *
  ext a
  simp
  by_cases h_ax : a = x
  · subst h_ax
    tauto
  · tauto

@[simp] lemma Proc.boundNames_bot (x y : PName) (P : Proc) (h : x ≠ y) :
  (x ∉ (y⸨⸩․P).boundNames) = (x ∉ (y⸨⸩․𝟘).boundNames ∪ P.boundNames) := by
  simp only [Proc.boundNames, Proc.names, Proc.f, Finset.union_empty] at *
  simp_all




@[simp] lemma Proc.f_subset_names (P : Proc) : P.f ⊆ P.names := by
  induction P <;> simp only [Proc.f, Proc.names]

  case nil | link | par | one | bot | selectL | selectR | amp | output
    | input | server | consume | dispose => gcongr

  case tensor ih | parr ih | duplicate ih =>
    intro a ha
    simp at ha ⊢
    rcases ha with rfl | ⟨hf, _⟩
    · left ; rfl
    · right ; right ; apply ih ; exact hf

  case cut ih =>
    intro a ha
    simp_all
    apply ih ; exact ha.1

@[simp] lemma Proc.not_mem_names_not_bound_free (x : PName) (P : Proc) (h : x ∉ P.names) :
  x ∉ P.boundNames ∪ P.f := by
  simp only [Proc.boundNames, Finset.sdiff_union_self_eq_union, Finset.notMem_union]
  apply And.intro
  · exact h
  · intro hf
    apply h
    apply Proc.f_subset_names
    exact hf






theorem Typing.subst_name (𝒢 : HyperEnv) (P : Proc) (𝒟 : ⊢ P ∷ 𝒢) (x z : PName)
  (hFresh : x ∉ 𝒢.names) (hSafe : x ∉ P.boundNames) :
  ⊢ (P{x // z}) ∷ (𝒢{x // z}) := by
  induction 𝒟

  case mix₀ =>
    simp only [HyperEnv.substName_empty, Proc.substname_nil]
    apply Typing.mix₀

  case mix 𝒢' ℋ' _ _ hDisj 𝒟 ℰ ihP ihQ =>
    rw [HyperEnv.names_merge, Finset.notMem_union] at hFresh
    simp only [← HyperEnv.substName_merge, ← Proc.substName_par]
    have this :  (𝒢'.substName x z).disjoint (ℋ'.substName x z) := by
      apply HyperEnv.substName_preserve_disjoint
      apply hDisj
      simp [Finset.biUnion_union] at ⊢ hFresh
      exact hFresh
    apply Typing.mix
    · exact this
    · apply ihP
      · exact hFresh.1
      · apply Proc.not_bound_par_left hSafe
        intro hxQf
        have hℋ' : x ∈ ℋ'.names := Typing.Pf_subset_HyperEnvNames ℰ hxQf
        exact hFresh.2 hℋ'
    · apply ihQ
      · exact hFresh.2
      · apply Proc.not_bound_par_right hSafe
        intro hxPf
        have h𝒢' : x ∈ 𝒢'.names := Typing.Pf_subset_HyperEnvNames 𝒟 hxPf
        exact hFresh.1 h𝒢'

  case ax =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton, Proc.substName_link]
    split
    · rename_i xp yp A hneq hxpz
      apply Typing.ax
      subst hxpz
      simp
      apply And.intro
      · exact hneq.symm
      · simp only [HyperEnv.names_distributes, Env.names_distributes,
          Env.names_singleton] at hFresh
        simp at hFresh
        exact hFresh.1
    · rename_i xp yp A hneq hxpnz
      apply Typing.ax
      simp only [HyperEnv.names_distributes, Env.names_distributes,
          Env.names_singleton] at hFresh
      split
      · simp at ⊢ hFresh
        intro h
        apply hFresh.right
        exact h.symm
      · exact hneq

  case one ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_singleton]
    simp [HasSubst.subst, Proc.substName]
    split
    all_goals
      apply Typing.one
      simp at ih ; apply ih
      rw [HyperEnv.names_singleton, Finset.mem_singleton] at hFresh
      simp_all [Proc.boundNames]

  case bot ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    simp only [HasSubst.subst, Proc.substName]
    split
    . apply Typing.bot
      · rename_i Γ P' xp hf1 hf2 _ hxpz
        subst hxpz
        change x ∉ Γ{x // xp}.names
        rw [Env.substName_eq_self_of_not_mem]
        simp only [HyperEnv.names_distributes, Env.names_distributes,
          Env.names_singleton, Finset.notMem_union] at hFresh
        · exact hFresh.1
        · exact hf1
      · rename_i Γ P' xp hf1 hf2 _ hxpz
        subst hxpz
        change x ∉ Γ{x // xp}.names
        rw [Env.substName_eq_self_of_not_mem]
        · simp only [HyperEnv.names_distributes, Env.names_distributes,
            Env.names_singleton, Finset.notMem_union] at hFresh
          exact hFresh.1
        · exact hf1
      · rename_i Γ P' xp hf1 hf2 _ hxpz
        subst hxpz
        simp only [HyperEnv.names_distributes, Env.names_distributes,
          Env.names_singleton, Finset.notMem_union, Finset.mem_singleton] at hFresh
        rw [Proc.boundNames_bot _ _ _ hFresh.2, Finset.notMem_union] at hSafe
        · apply ih
          · simp only [HyperEnv.names_distributes] ; exact hFresh.1
          · exact hSafe.2





    · apply Typing.bot
      rename_i Γ P' xp hf1 hf2 _ h1
      · change xp ∉ Γ{x // z}.names
        simp only [HyperEnv.names_distributes, Env.names_distributes,
          Env.names_singleton, Finset.notMem_union, Finset.mem_singleton] at hFresh
        sorry -- FIXME: Need lemma stating that if x ∉ Γ.names → x = x' → x ∉ Γ{x' // z}
      · sorry





    -- · simp at ih ; apply ih
    -- rw [HyperEnv.names_singleton, Finset.mem_singleton] at hFresh
    -- simp_all [Proc.boundNames]








  case bang h ih =>
    simp
    split
    all_goals
      rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.bang
      simp
      simp at hFresh ih
      specialize ih hFresh.1 hFresh.2
      split at ih
      · simp_all
      · simp_all
      · apply Env.serverUsable_subst
        exact h

  case c xp yp _ hneq h ih =>
    simp
    repeat split <;> try split
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.c <;> simp_all
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.c
      · intro h_contra
        subst h_contra
        simp at hSafe
        apply hneq.symm hSafe
      · rename_i hxpz hnypz
        subst hxpz
        simp_all
        apply ih
        intro h_contra
        subst h_contra
        simp at hSafe
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.c
      · simp_all
      · rename_i Γ' P' A hnxpz hypz
        subst hypz
        -- FIXME: Need statement about Proc bound names
        -- not being in the HyperEnv Typing them
        have hzNotΓ : yp ∉ Γ'.names := by sorry
        change ⊢ P' ∷ {Γ'{x // yp}‚ xp ∶ ??A‚ yp ∶ ??A}
        rw [Env.substName_eq_self_of_not_mem Γ' x yp hzNotΓ]
        exact h
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.c
      · simp_all
      · rename_i P' _ hnxpz hnypz
        simp at hFresh ih
        have hnxyp : x ≠ yp := by
          intro rfl
          apply hSafe
          simp [hneq.symm]
        have hxnP : (x ∈ P'.names → x ∈ P'.f) := by
          intro hxPp
          by_contra hnf
          apply hSafe
          simp
          constructor
          · right ;
            exact hxPp
          · constructor
            · exact hFresh.1
            · intro a
              contradiction
        specialize ih hnxyp hFresh.1 hFresh.2 hxnP
        simp [hnxpz, hnypz] at ⊢ ih
        exact ih

  case exists_ ih =>
    simp
    split
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.exists_
      rename_i Γ P' x' A B X D hxpz
      subst hxpz
      simp at ⊢ ih hFresh
      apply ih hFresh.1 hFresh.2 (by
        intro hxP ; simp at hSafe ; exact hSafe hxP hFresh.1)
    · rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.exists_
      rename_i Γ P' x' A B X D hxpz

      have this1 : x ∉ HyperEnv.names (Γ‚ x' ∶ B{A // X}) := by
        intro hxinn
        simp at hFresh
        simp only [HyperEnv.names] at hxinn
        rw [Finset.mem_biUnion] at hxinn
        rcases hxinn with ⟨E, hEset, hxE⟩
        simp only [Finset.mem_singleton] at hEset
        subst hEset
        rw [Env.names, Env.merge, Env.mk, Finset.image_union, Finset.image_singleton,
          Finset.mem_union, Finset.mem_singleton] at hxE
        rcases hxE with hΓ | rfl
        · rw [Finset.mem_image] at hΓ
          rcases hΓ with ⟨p, hpin, rfl⟩
          exact hFresh.2 _ hpin
        · exact hFresh.1 rfl

      have this2 : x ∉ P'.boundNames := by
        intro hxPpB
        simp at hSafe hxPpB
        rcases hxPpB with ⟨hinn, hnf⟩
        have hne : x ≠ x' := by
          intro rfl
          simp at this1
        have h_is_free : x ∈ P'.f := by
          exact hSafe hinn hne
        contradiction

      specialize ih this1 this2
      convert ih
      simp [Env.substName, hxpz]

  case forall_ ih =>
    simp only [HasSubst.subst, Proc.substName, HyperEnv.substName,
      Env.substName, Finset.image_singleton, Env.merge, Finset.image_union]
    split
    · rename_i Γ' P x' B X D p₂ hxz
      subst hxz
      have hneq : x ≠ x' := by
        intro rfl
        simp only [HyperEnv.names, Env.merge, Env.mk, Finset.union_singleton,
          Finset.singleton_biUnion, Finset.insert_eq, Env.names, Finset.image_union,
          Finset.image_singleton] at hFresh
        apply hFresh
        simp only [Finset.mem_union, Finset.mem_singleton]
        left
        exact True.intro

      simp only [← Finset.image_union]
      rw [Finset.insert_eq, Finset.union_comm]
      apply Typing.forall_
      simp at ih hFresh

      have this1 : (x ∈ P.names → x ∈ P.f) := by
        intro hxP










  case cut ih => sorry
  case tensor => sorry
  case parr => sorry


  -- FIXME: Remove just placeholder
  case bot | oplus₁ | oplus₂ | amp | quest | w => sorry

  -- FIXME: Broke after adding additional typing contraints
  -- case bot | oplus₁ | oplus₂ | amp | quest | w =>
  --   simp
  --   split
  --   all_goals
  --   · rw [Finset.insert_eq, Finset.union_comm]
  --     constructor <;> simp_all








theorem Typing.subst_types {𝒢 : HyperEnv} {P : Proc} {𝒟 : ⊢ P ∷ 𝒢}
  {A : Types} {X : TVar} : ⊢ (P.substTypes A X) ∷ (𝒢.substTypes A X) := by sorry

-- ------------------------------------------ LABELS ------------------------------------------

-- inductive Mu : Type
--   | L
--   | R
--   | DISP
--   | DUP
--   | USE
--   | A (t : Types)
-- deriving Repr, DecidableEq

-- inductive Act : Type
--   | one       (x : PName)               -- x[]
--   | bot       (x : PName)               -- x()
--   | tensor    (x y : PName)             -- x[y]
--   | parr      (x y : PName)             -- x(y)
--   | output    (x : PName) (A : Types)   -- x[A]
--   | input     (x : PName) (A : Types)   -- x(A)
--   | muBrack   (x : PName) (μ : Mu)      -- x[μ]
--   | muParen   (x : PName) (μ : Mu)      -- x[μ]
-- deriving Repr, DecidableEq

-- @[simp]
-- def fNamesAct : Act -> Finset PName -- free names
--   | .one x | .bot x
--   | .tensor x _ | .parr x _
--   | .input x _ | .output x _
--   | .muBrack x _  | .muParen x _ => {x}

-- @[simp]
-- def iNamesAct : Act → Finset PName -- introduced names
--   | .one _ | .bot _ | .input _ _ | .output _ _
--   | Act.muBrack _ _ | Act.muParen _ _ => ∅
--   | .tensor _ y | .parr _ y => {y}

-- inductive Lbl : Type
--   | tau                   -- τ
--   | link  (x y : PName)   -- x ⟷ y
--   | act   (p : Act)       -- l, for l ∈ Act
--   | par   (l l' : Act)    -- l | l' for l, l' ∈ Act, i(l) ∩ i(l') = ∅ (.WF)
-- deriving Repr, DecidableEq

-- abbrev Lbls := List Lbl

-- instance : Coe Act Lbl := ⟨Lbl.act⟩

-- @[simp]
-- def Lbl.WF : Lbl → Prop
--   | .tau => True
--   | .link _ _ => True
--   | .act _ => True
--   | .par l l' => (iNamesAct l) ∩ (iNamesAct l') = ∅

-- @[simp]
-- def Lbl.f : Lbl → Finset PName
--   | .tau        => ∅
--   | .link x y   => {x, y}
--   | .act a      => fNamesAct a
--   | .par l l'   => fNamesAct l ∪ fNamesAct l'

-- @[simp]
-- def Lbl.i : Lbl → Finset PName
--   | .tau        => ∅
--   | .link _ _   => ∅
--   | .act a      => iNamesAct a
--   | .par l l'   => iNamesAct l ∪ iNamesAct l'

-- @[simp]
-- def Lbl.fresh (xs : List PName) (l : Lbl) :=
--   ∀ n ∈ xs, n ∉ l.f ∪ l.i

-- notation "𝐋"    => Mu.L
-- notation "𝐑"    => Mu.R
-- notation "USE"  => Mu.USE
-- notation "DUP"  => Mu.DUP
-- notation "DISP" => Mu.DISP

-- notation:80 x"⟦⟧" => HasBracket.brack x ()
-- notation:80 x"⟦"y"⟧" => HasBracket.brack x y

-- @[simp] instance : HasBracket PName Unit Act where brack x _ := Act.one x
-- @[simp] instance : HasBracket PName PName Act where brack x y := Act.tensor x y
-- @[simp] instance : HasBracket PName Types Act where brack x A := Act.output x A
-- @[simp] instance : HasBracket PName Mu Act where brack x μ := Act.muBrack x μ

-- notation:80 x"⸨⸩" => HasParen.paren x ()
-- notation:80 x"⸨"y"⸩" => HasParen.paren x y

-- @[simp] instance : HasParen PName Unit Act where paren x _ := Act.bot x
-- @[simp] instance : HasParen PName PName Act where paren x y := Act.parr x y
-- @[simp] instance : HasParen PName Types Act where paren x A := Act.input x A
-- @[simp] instance : HasParen PName Mu Act where paren x μ := Act.muParen x μ

-- -- Tells Lean to use (HasBracket / HasParen) Act when asked for the Lbl variant
-- @[simp] instance {S C : Type} [HasBracket S C Act] : HasBracket S C Lbl where
--   brack s c := Lbl.act (HasBracket.brack s c)

-- @[simp] instance {S C : Type} [HasParen S C Act] : HasParen S C Lbl where
--   paren s c := Lbl.act (HasParen.paren s c)

-- notation:80 x "⟷ₗ" y => Lbl.link x y
-- notation:70 l " |ₗ " l' => Lbl.par l l'
-- notation:80 "τ" => Lbl.tau

-- @[app_unexpander Lbl.act]
-- def unexpandLblAct : Lean.PrettyPrinter.Unexpander
--   | `($_ $a) => pure a
--   | _ => throw ()

-- ----------------------------- TRANSITION RULES FOR DERIVATIONS -----------------------------

-- inductive TypingStep : {𝒢 : HyperEnv} → {P : Proc} → Typing 𝒢 P →
--   Lbl → {𝒢' : HyperEnv} → {P' : Proc} → Typing 𝒢' P' → Prop where
--   | one
--       {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ ∅} :
--       TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

--   | tensor
--       {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B} :
--       TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

--   | bot
--       {Γ : Env} {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ Γ} :
--       TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

--   | parr
--       {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A‚ x ∶ B} :
--       TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

--   | par₁
--       {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'} {ℰ : ⊢ Q ∷ ℋ}
--       (h : TypingStep 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
--       -----------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

--   | par₂
--       {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h : TypingStep ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
--       ----------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

--   | syn
--       {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act}
--       {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'}
--       {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h₁ : TypingStep 𝒟 l 𝒟') (h₂ : TypingStep ℰ l' ℰ')
--       (disj : (l |ₗ l').i ∩ (P |ₚ Q).f = ∅)
--       (WF : (l |ₗ l').WF) : -- FIXME: show TypingStep preserves WF without this
--       ---------------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) (l |ₗ l') (Typing.mix 𝒟' ℰ')

--   | alpha_equiv
--       {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ 𝒢} {ℰ' : ⊢ Q' ∷ 𝒢'}
--       (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
--       -----------------------------------------------
--       TypingStep 𝒟 l ℰ'

--   | one_bot
--       {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
--       {𝒟 : ⊢ P ∷  𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥} {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ}
--       (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
--       -------------------------------------------------------
--       TypingStep (Typing.cut 𝒢 ∅ Γ P x y (1) 𝒟) (τ) 𝒟'

--   | tensor_parr
--       {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ x' ∶ A |ₕ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ}
--       (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
--       ----------------------------------------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 (Γ‚ Δ) Ξ P x y (A ⨂ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ (Δ‚ Ξ) (𝑣⸨x', y'⸩ P') x y B
--           (by
--            let inner := Typing.cut (𝒢 |ₕ {Γ‚ x ∶ B}) Δ (Ξ‚ y ∶ Bᗮ) P' x' y' A 𝒟'
--            rw [← Env.merge_assoc] at inner
--            exact inner
--           )
--         )

--   | res
--       {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
--       {x y : PName} {A : Types} {l : Lbl}
--       {𝒟 : Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P}
--       {𝒟' : Typing (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ) P'}
--       (h : TypingStep 𝒟 l 𝒟') (disj : l.fresh [x, y]) :
--       ----------------------------------------------------------------------------
--       TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')

--   | selectL
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} :
--       TypingStep (Typing.oplus₁ (B := B) 𝒟) (x⟦𝐋⟧) 𝒟

--   | selectR
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.oplus₂ (A := A) 𝒟) (x⟦𝐑⟧) 𝒟

--   | ampL
--       {Γ : Env} {P Q : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {ℰ : ⊢ Q ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.amp 𝒟 ℰ) (x⸨𝐋⸩) 𝒟

--   | ampR
--       {Γ : Env} {P Q : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {ℰ : ⊢ Q ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.amp 𝒟 ℰ) (x⸨𝐑⸩) ℰ

--   | selectL_amp
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ A ⊕ B |ₕ Δ‚ y ∶ Aᗮ & Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ} :
--       TypingStep 𝒟 (x⟦𝐋⟧ |ₗ y⸨𝐋⸩) 𝒟' →
--       -------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (A ⊕ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y A 𝒟')

--   | selectR_amp
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ A ⊕ B |ₕ Δ‚ y ∶ Aᗮ & Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ y ∶ Bᗮ} :
--       TypingStep 𝒟 (x⟦𝐑⟧ |ₗ y⸨𝐑⸩) 𝒟' →
--       --------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (A ⊕ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y B 𝒟')

--   | output
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B{A // X}} :
--       TypingStep (Typing.exists_ 𝒟) (x⟦A⟧) 𝒟

--   | input -- FIXME: Might need typing subst for judgements, test if current is ok
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B} {h : X ∉ ft(Γ)}
--       -- TypingStep (Typing.forall_ (X := X) 𝒟 h) (x⸨A⸩:) (𝒟{A // X}) --------------------------------------------------------------------------
--       {𝒟' : ⊢ P{A // X} ∷ Γ‚ x ∶ B{A // X}} :
--       TypingStep (Typing.forall_ (X := X) 𝒟 h) (x⸨A⸩) 𝒟'

--   | input_output
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ (∃X․B) |ₕ Δ‚ y ∶ ∀X․Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B{A // X} |ₕ Δ‚ y ∶ Bᗮ{A // X}} :

--       TypingStep 𝒟 (x⟦A⟧ |ₗ y⸨A⸩) 𝒟' →
--       -----------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (∃X․B) 𝒟)
--         (τ)
--         (by
--           rw [Types.subst_dual] at 𝒟'
--           exact Typing.cut 𝒢 Γ Δ P' x y (B{A // X}) 𝒟'
--         )

--   | link₁
--       {x y : PName} {A : Types} :
--       TypingStep (Typing.ax (x := x) (y := y) (A := A)) (x ⟷ₗ y) (Typing.mix₀)

--   | link₂
--       {x y : PName} {A : Types} :
--       TypingStep (Typing.ax (x := x) (y := y) (A := A)) (y ⟷ₗ x) (Typing.mix₀)

--   -- NOTE: Only free names can perform actions => HyperEnv only contains free names
--   -- => Renaming of a bound variable only needs to happen in the process term
--   | axcut -- FIXME: Might need typing subst for judgements, test if current is ok
--       {𝒢 : HyperEnv} {Γ : Env} {P P' : Proc} {x y z : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ x ∶ Aᗮ‚ y ∶ A |ₕ Γ‚ z ∶ Aᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ z ∶ Aᗮ}
--       {𝒟'σ : ⊢ P'{x // z} ∷ 𝒢 |ₕ Γ‚ x ∶ Aᗮ} :
--       TypingStep 𝒟 (x ⟷ₗ y) 𝒟' →
--       -----------------------------------
--       TypingStep
--       (Typing.cut 𝒢 (x ∶ Aᗮ) Γ P y z A 𝒟)
--       (τ)
--       -- (𝒟'{x // z}) --------------------------------------------------------------------------------------------------------------------------
--       (𝒟'σ)

--   | quest
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} :
--       TypingStep (Typing.quest 𝒟) (x⟦USE⟧) 𝒟

--   | bang
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {h : ?ₑΓ} :
--       TypingStep (Typing.bang 𝒟 h) (x⸨USE⸩) 𝒟

--   | bang_quest
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ} :
--       TypingStep 𝒟 (x⟦USE⟧ |ₗ x⸨USE⸩) 𝒟' →
--       ------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y A 𝒟')

--   | dup₁
--       {Γ : Env} {P : Proc} {x x' : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ ??A‚ x' ∶ ??A} :
--       TypingStep (Typing.c 𝒟) (x⟦DUP⟧) (Typing.parr 𝒟)

--   -- FIXME: Needs sigma to be applicable to Proc and Env
--   -- FIXME: Theorem stating subst preserves serverUsable
--   | dup₂
--       {Γ Γσ : Env} {P Pσ : Proc} {x xσ : PName} {A : Types}
--       {names namesσ: List PName} {σ : Renaming}
--       -- NOTE: All the postfix σ variables are only here until σ can be applied to them
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} (h₁ : ?ₑΓ)
--       {𝒟σ : ⊢ Pσ ∷ Γσ‚ xσ ∶ A} (h₂ : ?ₑΓσ)
--       -- NOTE: Maybe don't need ?Γσ since it only contains a name for each dependency in Γ
--       -- which all get paired of (z, zσ), so ?Γσ is consumed during the repeated application
--       -- of the c-rule but there might still be some non-dependencies in Γ, so we keep it?
--       {𝒟σ' : ⊢ (x⟦xσ⟧․(!xσ․{Pσ} |ₚ !x․{P})).open namesσ σ ∷ Γ‚ x ∶ !!Aᗮ ⨂ !!Aᗮ} :
--       P.f ∩ (P.f.image σ) = ∅ →
--       names = (P.f \ {x}).toList.mergeSort (· ≤ ·) →
--       -------------------------------------------------------------------------
--       TypingStep
--         (Typing.bang 𝒟 h₁)
--         (x⸨DUP⸩)
--         -- (Typing.c_ALT? (Typing.tensor (Typing.mix (Typing.bang 𝒟σ h₂) (Typing.bang 𝒟 h₁)))) ------------------------------------------------
--         (𝒟σ')

--   | bang_c
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ} (h : ?ₑΔ)
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ ??A ⅋ ??A |ₕ Δ‚ y ∶ !!Aᗮ ⨂ !!Aᗮ} :
--       TypingStep 𝒟 (x⟦DUP⟧ |ₗ x⸨DUP⸩) 𝒟' →
--       -------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y (??A ⅋ ??A) 𝒟')

--   | dispose
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ} :
--       TypingStep
--         (Typing.w (x := x) (A := A) 𝒟)
--         (x⟦DISP⟧)
--         (Typing.bot (x := x) 𝒟)

--   | dispose₂ -- FIXME
--       {Γ : Env} {P : Proc} {x x' : PName} {A : Types} {names : List PName}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} (h : ?ₑΓ)
--       {𝒟' : ⊢ (x⟦⟧․𝟘).close names ∷ Γ‚ x ∶ 1} :
--       (P.f \ {x}).toList.mergeSort (· ≤ ·) = names →
--       -----------------------------------------------
--       TypingStep
--         (Typing.bang 𝒟 h)
--         (x⸨DISP⸩)
--         𝒟'

--   | bang_w
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ} (h : ?ₑΔ)
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ ⊥ |ₕ Δ‚ y ∶ 1} :
--       TypingStep 𝒟 (x⟦DISP⟧ |ₗ x⸨DISP⸩) 𝒟' →
--       --------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y ⊥ 𝒟')


-- notation:50 𝒟 " -[" l "]->ₜ " 𝒟' => TypingStep 𝒟 l 𝒟'

-- theorem TypingStep.preserves_WF (𝒢 𝒢' : HyperEnv) (P P' : Proc)
--   (𝒟 : ⊢ P ∷ 𝒢) (𝒟' : ⊢ P' ∷ 𝒢') (l : Lbl) :
--   TypingStep 𝒟 l 𝒟' → l.WF := by
--   intro h
--   induction h <;> simp_all [Lbl.WF]


-- -- theorem TypingStep.preserves_serverUsableEnv


-- notation:80 "ε" => (List.nil : Lbls)
-- notation:60 xs " ∷ₗ " x => List.concat (xs : Lbls) (x : Lbl)

-- lemma eq_concat_nil {l} :
--   [l] = (ε ∷ₗ l) := by rfl

-- lemma cons_concat_eq {x xs y} :
--   x :: (xs ∷ₗ y) = x :: (xs ∷ₗ y) := by simp

-- lemma append_concat_eq {xs ys y} :
--   xs ++ (ys ∷ₗ y) = (xs ++ ys) ∷ₗ y := by simp

-- lemma cons_append_assoc {x : Lbl} {xs ys : Lbls} :
--   x :: (xs ++ ys) = (x :: xs) ++ ys := by rfl

-- inductive MTST : {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
--   Typing 𝒢 P → Lbls → Typing 𝒢' P' → Prop where
--   | refl
--     {𝒢 : HyperEnv} {P: Proc} {𝒟 : Typing 𝒢 P} :
--     MTST 𝒟 (ε) 𝒟

--   | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
--     (𝒟  : Typing 𝒢  P) (𝒟' : Typing 𝒢' P') (𝒟'' : Typing 𝒢'' P'') :
--     (MTST 𝒟 ls 𝒟'') → (𝒟'' -[l]->ₜ 𝒟') →
--     -------------------------------------
--           MTST 𝒟 (ls ∷ₗ l) 𝒟'

-- notation:50 𝒟 " -[" ls "]->>ₜ " 𝒟' => MTST 𝒟 ls 𝒟'

-- ------------------------- PROC-FUCNTION & TRANSITION RULES -------------------------

-- def proc {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : Proc := P

-- inductive ProcStep : (P : Proc) → Lbl → (P' : Proc) → Prop where
--   | one
--       {P : Proc} {x : PName} :
--       ProcStep (x⟦⟧․P) (x⟦⟧) P

--   | tensor
--       {P : Proc} {x x' : PName} :
--       ProcStep (x⟦x'⟧․P) (x⟦x'⟧) P

--   | bot
--       {P : Proc} {x : PName} :
--       ProcStep (x⸨⸩․P) (x⸨⸩) P

--   | parr
--       {P : Proc} {x x' : PName} :
--       ProcStep (x⸨x'⸩․P) (x⸨x'⸩) P

--   | par₁
--       {P P' Q : Proc} {l : Lbl} :
--       ProcStep P l P' → l.i ∩ Q.f = ∅ →
--       ----------------------------------
--       ProcStep (P |ₚ Q) l (P' |ₚ Q)

--   | par₂
--       {P Q Q' : Proc} {l : Lbl} :
--       ProcStep Q l Q' → l.i ∩ P.f = ∅ →
--       ----------------------------------
--       ProcStep (P |ₚ Q) l (P |ₚ Q')

--   | syn
--       {P P' Q Q' : Proc} {l l' : Act} :
--       ProcStep P l P' → ProcStep Q l' Q' →
--       (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  → (l |ₗ l').WF →
--       ---------------------------------------------
--       ProcStep (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

--   | alpha_equiv
--       {P Q Q' : Proc} {l : Lbl} :
--       (P =ₐ Q) → ProcStep Q l Q' →
--       -------------------------------
--       ProcStep P l Q'

--   | one_bot
--       {P P' : Proc} {x y : PName} :
--       ProcStep P (x⟦⟧ |ₗ y⸨⸩) P' →
--       ----------------------------
--       ProcStep (𝑣⸨x, y⸩ P) (τ) P'

--   | tensor_parr
--       {P P' : Proc} {x x' y y' : PName} :
--       ProcStep P (x⟦x'⟧ |ₗ y⸨y'⸩) P' →
--       -------------------------------------------------
--       ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ (𝑣⸨x', y'⸩ P'))

--   | res
--       {P P' : Proc} {x y : PName} {l : Lbl} :
--       ProcStep P l P' → l.fresh [x, y] →
--       -------------------------------------
--       ProcStep (𝑣⸨x, y⸩ P) (l) (𝑣⸨x, y⸩ P')

--   | disp₁
--       {P : Proc} {x : PName} :
--       ProcStep (x⟦DISP⟧․P) (x⟦DISP⟧) (x⸨⸩․P)

--   | disp₂
--       {P : Proc} {x : PName} {names : List PName} :
--       (P.f \ {x}).toList.mergeSort (· ≤ ·) = names →
--       --------------------------------------------------
--       ProcStep (!x․{P}) (x⸨DISP⸩) ((!x․{P}).close names)

--   | dup₁
--       {P : Proc} {x x' : PName} :
--       ProcStep (x⟦DUP⟧⸨x'⸩․P) (x⟦DUP⟧) (x⸨x'⸩․P)

--   | dup₂
--       {P : Proc} {x x' : PName} {names : List PName} {σ : Renaming} :
--       P.f ∩ (P.f.image σ) = ∅ → names = (P.f \ {x}).toList.mergeSort (· ≤ ·) →
--       -------------------------------------------------------------------------
--       ProcStep (!x․{P}) (x⸨DUP⸩) ((!x․{P}).open names σ)

--   | use₁
--       {P : Proc} {x : PName} :
--       ProcStep (x⟦USE⟧․P) (x⟦USE⟧) P

--   | use₂
--       {P : Proc} {x : PName} :
--       ProcStep (!x․{P}) (x⸨USE⸩) P

--   | output
--       {P : Proc} {x : PName} {A : Types} :
--       ProcStep (x⟦A⟧․P) (x⟦A⟧) P

--   | input
--       {P : Proc} {x : PName} {A : Types} {X : TVar}:
--       ProcStep (x⸨X⸩․P) (x⸨A⸩) (P{A // X})

--   | selectL
--       {P : Proc} {x : PName} :
--       ProcStep (x⟦𝐋⟧․P) (x⟦𝐋⟧) P

--   | ampL
--       {P Q : Proc} {x : PName} :
--       ProcStep (x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐋⸩) P

--   | selectR
--       {P : Proc} {x : PName} :
--       ProcStep (x⟦𝐑⟧․P) (x⟦𝐑⟧) P

--   | ampR
--       {P Q : Proc} {x : PName} :
--       ProcStep (x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐑⸩) Q

--   | link₁
--       {x y : PName} :
--       ProcStep (x ⟷ₚ y) (x ⟷ₗ y) 𝟘

--   | link₂
--       {x y : PName} :
--       ProcStep (x ⟷ₚ y) (y ⟷ₗ x) 𝟘

--   | com {P P' : Proc} {x y : PName} {μ : Mu} :
--       ProcStep P (x⟦μ⟧ |ₗ y⟦μ⟧) P' →
--       -------------------------------------
--       ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ P')

--   | axcut
--       {P P' : Proc} {x y z : PName} :
--       ProcStep P (x ⟷ₗ y) P' →
--       --------------------------------------
--       ProcStep (𝑣⸨y, z⸩ P) (τ) (P'{x // z})

-- notation:50 P " -[" l "]->ₚ " P' => ProcStep P l P'

-- theorem ProcStep.preserves_WF (P P' : Proc) (l : Lbl) :
--   ProcStep P l P' → l.WF := by
--   intro h
--   induction h <;> simp_all [Lbl.WF]

-- inductive MPST : (P : Proc) → Lbls → (P' : Proc) → Prop where
--   | refl
--     {P : Proc} :
--     ------------
--     MPST P (ε) P

--   | stepR {l : Lbl} {ls : Lbls} {P P'' P' : Proc} :
--     (MPST P ls P'') → (P'' -[l]->ₚ P') →
--     ------------------------------------
--           MPST P (ls ∷ₗ l) P'

-- notation:50 P " -[" ls "]->>ₚ " P' => MPST P ls P'

-- ------------------------- ENV-FUCNTION & TRANSITION RULES --------------------------

-- def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

-- inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
--   | one
--       {x : PName} :
--       EnvStep (x ∶ 1) (x⟦⟧) ∅

--   | tensor
--       {Γ Δ : Env} {x x' : PName} {A B : Types} :
--       EnvStep (Γ‚ Δ‚ x ∶ A ⨂ B) (x⟦x'⟧) (Γ‚ x'∶ A |ₕ Δ‚ x ∶ B)

--   | bot
--       {Γ : Env} {x : PName} :
--       EnvStep (Γ‚ x ∶ ⊥) (x⸨⸩) Γ

--   | parr
--       {Γ Δ : Env} {x x' : PName} {A B : Types} :
--       EnvStep (Γ‚ x ∶ A ⅋ B) (x⸨x'⸩) (Γ‚ x' ∶ A‚ Δ‚ x ∶ B)

--   | par₁
--       {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
--       EnvStep 𝒢 l 𝒢' →
--       -----------------------------
--       EnvStep (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

--   | par₂
--       {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
--       EnvStep ℋ l ℋ' →
--       -----------------------------
--       EnvStep (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

--   | syn
--       {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
--       EnvStep 𝒢 l 𝒢' → EnvStep ℋ l' ℋ' → (l |ₗ l').WF →
--       --------------------------------------------------
--       EnvStep (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')

--   | one_bot
--       {𝒢 : HyperEnv} {Γ : Env} {x y : PName} :
--       EnvStep (𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ Γ) →
--       ------------------------------------------------------
--       EnvStep (𝒢 |ₕ Γ) (τ) (𝒢 |ₕ Γ)

--   | tensor_parr
--       {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': PName} {A B : Types} :
--       EnvStep
--         (𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ)
--         (x⟦x'⟧ |ₗ y⸨y'⸩)
--         (𝒢 |ₕ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B |ₕ Ξ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) →
--       ---------------------------------------------------
--       EnvStep (𝒢 |ₕ Γ‚ Δ‚ Ξ) (τ) (𝒢 |ₕ Γ‚ Δ‚ Ξ)

--   | res
--       {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : PName} {A B : Types} {l : Lbl} :
--       EnvStep (𝒢 |ₕ Γ‚ x ∶ Aᗮ |ₕ Δ‚ y ∶ A) (l) (𝒢' |ₕ Γ'‚ x ∶ Aᗮ |ₕ Δ'‚ y ∶ A) →
--       ----------------------------------------------------------------------------
--       EnvStep (𝒢 |ₕ Γ‚ Δ) l (𝒢' |ₕ Γ'‚ Δ')

--   | selectL
--       {Γ : Env} {x : PName} {A B : Types} :
--       EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧) (Γ‚ x ∶ A)

--   | ampL
--       {Γ : Env} {x : PName} {A B : Types} :
--       EnvStep (Γ‚ x ∶ A & B) (x⸨𝐋⸩) (Γ‚ x ∶ A)

--   | selectR
--       {Γ : Env} {x : PName} {A B : Types} :
--       EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧) (Γ‚ x ∶ B)

--   | ampR
--       {Γ : Env} {x : PName} {A B : Types} :
--       EnvStep (Γ‚ x ∶ A & B) (x⸨𝐑⸩) (Γ‚ x ∶ B)

--   | link₁
--       {x y : PName} {A : Types} :
--       EnvStep (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₗ y) ∅

--   | link₂ -- FIXME this one isn't actually in the definition in Fig 8, but it matches ProcStep
--       {x y : PName} {A : Types} :
--       EnvStep (x ∶ Aᗮ‚ y ∶ A) (y ⟷ₗ x) ∅

--   | use₁
--       {Γ : Env} {x : PName} {A : Types} :
--       EnvStep (Γ‚ x ∶ ??A) (x⟦USE⟧) (Γ‚ x ∶ A)

--   | use₂
--       {Γ : Env} {x : PName} {A : Types} :
--       ?ₑΓ →
--       --------------------------------------
--       EnvStep (Γ‚ x ∶ !!A) (x⸨USE⸩) (Γ‚ x ∶ A)

--   | disp₁
--       {Γ : Env} {x : PName} {A : Types} :
--       EnvStep (Γ‚ x ∶ ??A) (x⟦DISP⟧) (Γ‚ x ∶ ⊥)

--   | disp₂
--       {Γ : Env} {x : PName} {A : Types} :
--       EnvStep {Γ‚ x ∶ !!A} (x⸨DISP⸩) (Γ‚ x ∶ 1)

--   | dup₁
--       {Γ : Env} {x : PName} {A : Types} :
--       EnvStep (Γ‚ x ∶ ??A) (x⟦DUP⟧) (Γ‚ x ∶ ??A ⅋ ??A)

--   | dup₂
--       {Γ : Env} {x : PName} {A : Types} :
--       ?ₑΓ →
--       ----------------------------------------------
--       EnvStep (Γ‚ x ∶ !!A) (x⸨DUP⸩) (Γ‚ x ∶ !!A ⨂ !!A)

--   | output
--       {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
--       EnvStep (Γ‚ x ∶ ∃X․B) (x⟦A⟧) (Γ‚ x ∶ B{A // X})

--   | input
--       {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
--       EnvStep (Γ‚ x ∶ ∀X․B) (x⸨A⸩) (Γ‚ x ∶ B{A // X})

-- notation:50 P " -[" l "]->ₑ " P' => EnvStep P l P'

-- theorem EnvStep.preserves_WF (Γ Γ' : HyperEnv) (l : Lbl) :
--   EnvStep Γ l Γ' → l.WF := by
--   intro h
--   induction h <;> simp_all [Lbl.WF]

-- inductive MEST : (𝒢 : HyperEnv) → Lbls → (𝒢' : HyperEnv) → Prop where
--   | refl
--     {𝒢 : HyperEnv} :
--     -------------
--     MEST 𝒢 (ε) 𝒢

--   | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢'' 𝒢' : HyperEnv} :
--     (MEST 𝒢 ls 𝒢'') → (𝒢'' -[l]->ₑ 𝒢') →
--     ------------------------------------
--           MEST 𝒢 (ls ∷ₗ l) 𝒢'

-- notation:50 𝒢 " -[" ls "]->>ₑ " 𝒢' => MPST 𝒢 ls 𝒢'
