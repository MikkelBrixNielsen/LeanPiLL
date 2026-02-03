import PiLL.Framework.Model.Process

inductive Mu : Type
  | L
  | R
  | DISP
  | DUP
  | USE
  | A (t : Types)
deriving Repr, DecidableEq

inductive Act : Type
  | one       (x : FPName)               -- x[]
  | bot       (x : FPName)               -- x()
  | tensor    (x y : FPName)             -- x[y]
  | parr      (x y : FPName)             -- x(y)
  | output    (x : FPName) (A : Types)   -- x[A]
  | input     (x : FPName) (A : Types)   -- x(A)
  | muBrack   (x : FPName) (μ : Mu)      -- x[μ]
  | muParen   (x : FPName) (μ : Mu)      -- x[μ]
deriving Repr, DecidableEq

@[simp]
def fNamesAct : Act -> Finset FPName -- free names
  | .one x | .bot x
  | .tensor x _ | .parr x _
  | .input x _ | .output x _
  | .muBrack x _  | .muParen x _ => {x}

@[simp]
def iNamesAct : Act → Finset FPName -- introduced names
  | .one _ | .bot _ | .input _ _ | .output _ _
  | Act.muBrack _ _ | Act.muParen _ _ => ∅
  | .tensor _ y | .parr _ y => {y}

inductive Lbl : Type
  | tau                   -- τ
  | link  (x y : FPName)   -- x ⟷ y
  | act   (p : Act)       -- l, for l ∈ Act
  | par   (l l' : Act)    -- l | l' for l, l' ∈ Act, i(l) ∩ i(l') = ∅ (.WF)
deriving Repr, DecidableEq

abbrev Lbls := List Lbl

instance : Coe Act Lbl := ⟨Lbl.act⟩

@[simp]
def Lbl.WF : Lbl → Prop
  | .tau => True
  | .link _ _ => True
  | .act _ => True
  | .par l l' => (iNamesAct l) ∩ (iNamesAct l') = ∅

@[simp]
def Lbl.f : Lbl → Finset FPName
  | .tau        => ∅
  | .link x y   => {x, y}
  | .act a      => fNamesAct a
  | .par l l'   => fNamesAct l ∪ fNamesAct l'

@[simp]
def Lbl.i : Lbl → Finset FPName
  | .tau        => ∅
  | .link _ _   => ∅
  | .act a      => iNamesAct a
  | .par l l'   => iNamesAct l ∪ iNamesAct l'

@[simp]
def Lbl.fresh (xs : List FPName) (l : Lbl) :=
  ∀ n ∈ xs, n ∉ l.f ∪ l.i

notation "𝐋"    => Mu.L
notation "𝐑"    => Mu.R
notation "USE"  => Mu.USE
notation "DUP"  => Mu.DUP
notation "DISP" => Mu.DISP

notation:80 x"⟦⟧" => HasBracket.brack x ()
notation:80 x"⟦"y"⟧" => HasBracket.brack x y

@[simp] instance : HasBracket FPName Unit Act where brack x _ := Act.one x
@[simp] instance : HasBracket FPName FPName Act where brack x y := Act.tensor x y
@[simp] instance : HasBracket FPName Types Act where brack x A := Act.output x A
@[simp] instance : HasBracket FPName Mu Act where brack x μ := Act.muBrack x μ

notation:80 x"⸨⸩" => HasParen.paren x ()
notation:80 x"⸨"y"⸩" => HasParen.paren x y

@[simp] instance : HasParen FPName Unit Act where paren x _ := Act.bot x
@[simp] instance : HasParen FPName FPName Act where paren x y := Act.parr x y
@[simp] instance : HasParen FPName Types Act where paren x A := Act.input x A
@[simp] instance : HasParen FPName Mu Act where paren x μ := Act.muParen x μ

-- Tells Lean to use (HasBracket / HasParen) Act when asked for the Lbl variant
@[simp] instance {S C : Type} [HasBracket S C Act] : HasBracket S C Lbl where
  brack s c := Lbl.act (HasBracket.brack s c)

@[simp] instance {S C : Type} [HasParen S C Act] : HasParen S C Lbl where
  paren s c := Lbl.act (HasParen.paren s c)

notation:80 x "⟷ₗ" y => Lbl.link x y
notation:70 l " |ₗ " l' => Lbl.par l l'
notation:80 "τ" => Lbl.tau

@[app_unexpander Lbl.act]
def unexpandLblAct : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => pure a
  | _ => throw ()

notation:80 "ε" => (List.nil : Lbls)
notation:60 xs " ∷ₗ " x => List.concat (xs : Lbls) (x : Lbl)

lemma eq_concat_nil {l} :
  [l] = (ε ∷ₗ l) := by rfl

lemma cons_concat_eq {x xs y} :
  x :: (xs ∷ₗ y) = x :: (xs ∷ₗ y) := by simp

lemma append_concat_eq {xs ys y} :
  xs ++ (ys ∷ₗ y) = (xs ++ ys) ∷ₗ y := by simp

lemma cons_append_assoc {x : Lbl} {xs ys : Lbls} :
  x :: (xs ++ ys) = (x :: xs) ++ ys := by rfl
