import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

abbrev Atom := Nat

inductive Types : Type where
  | atom (a : Atom)
  | atomDual (a : Atom)
  | one
  | bot

instance : One Types := ⟨Types.one⟩
instance : Bot Types := ⟨Types.bot⟩

def Types.dual : Types → Types
  | one => bot
  | bot => one
  | atom a => atomDual a
  | atomDual a => atom a

postfix:max "ᗮ" => Types.dual

abbrev PName := Nat

inductive Proc : Type where
  | nil
  | one (x : PName) (P : Proc)
  | bot (x : PName) (P : Proc)
  | par (P Q : Proc)
  | cut (x y : PName) (P : Proc)


notation:80 x "⟦⟧․" P => Proc.one x P
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 "𝑣⸨"x"," y"⸩"P => Proc.cut x y P
notation "𝟘" => Proc.nil
infixr:50 "|ₚ" => Proc.par

abbrev Env := List (PName × Types)
def Env.mk (x : PName) (A : Types) := [(x, A)]
notation:80 x "∶" A => Env.mk x A

inductive Split : Env → Env → Env → Prop where
  | nil : Split ∅ ∅ ∅

  | left (x A Γ Γ₁ Γ₂) :
      Split Γ Γ₁ Γ₂ →
      Split ((x, A) :: Γ) ((x, A) :: Γ₁) Γ₂

  | right (x A Γ Γ₁ Γ₂) :
      Split Γ Γ₁ Γ₂ →
      Split ((x, A) :: Γ) Γ₁ ((x, A) :: Γ₂)


inductive Typing : Proc → Env → Prop where
  | mix₀ :
    Typing 𝟘 ∅

  | mix {P Q : Proc} {Γ Γ₁ Γ₂ : Env} :
    Split Γ Γ₁ Γ₂ → Typing P Γ₁ → Typing Q Γ₂ →
    Typing (P |ₚ Q) Γ

  | one {x : PName} {P : Proc} :
    Typing (x⟦⟧․P) (x ∶ 1)


inductive Lbl : Type where
  | one (x : PName)
  | bot (x : PName)

inductive ProcStep : Proc → Lbl → Proc → Prop where
  | one {x : PName} {P : Proc} :
    ProcStep (x⟦⟧․P) (Lbl.one x) P

  | par₁ {P P' Q : Proc} {l : Lbl}:
    ProcStep P l P' →
    ProcStep (P |ₚ Q) l (P' |ₚ Q)

  | res
      {P P' : Proc} {x y : PName} {l : Lbl} :
      ProcStep P l P' →
      ProcStep (𝑣⸨x, y⸩ P) (l) (𝑣⸨x, y⸩ P')

inductive EnvStep : Env → Lbl → Env → Prop where
  | one {x : PName} :
    EnvStep (x ∶ 1) (Lbl.one x) ∅

 | par₁
    {𝒢 𝒢' Γ Γ' Δ : Env} {l : Lbl} :
    Split 𝒢 Γ Δ → EnvStep Γ l Γ' →
    Split 𝒢' Γ' Δ → EnvStep 𝒢 l 𝒢'

  | res {𝒢 𝒢' E𝒢'Γx 𝒢' EΓx Γ EΔy Δ : Env} {x y : PName} {A : Types} {l : Lbl}:
    Split EΓx Γ (x ∶ Aᗮ) → Split EΔy (Δ) (y ∶ A) → Split E𝒢'Γx 𝒢' EΓx →
    Split 𝒢 E𝒢'Γx EΔy →


    EnvStep 𝒢 l 𝒢' →
