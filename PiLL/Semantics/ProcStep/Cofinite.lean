import PiLL.Model.Processes.Notation
import PiLL.Model.Processes.Names
import PiLL.Model.Processes.OpenClose
import PiLL.Semantics.Labels

inductive ProcStepₘ : (P : Proc) → Lbl → (P' : Proc) → Prop where
  | one
      {P : Proc} {x : FPName} :
      ProcStepₘ (#x⟦⟧․P) (x⟦⟧) P
  | tensor
      {P : Proc} {x y : FPName} (hF : y ∉ {x} ∪ P.f) :
      ProcStepₘ (#x⟦•⟧․P) (x⟦y⟧) P⸨#y⸩
  | bot
      {P : Proc} {x : FPName} :
      ProcStepₘ (#x⸨⸩․P) (x⸨⸩) P
  | parr
      {P : Proc} {x y : FPName} (hF: y ∉ {x} ∪ P.f) :
      ProcStepₘ (#x⸨•⸩․P) (x⸨y⸩) P⸨#y⸩
  | par₁
      {P P' Q : Proc} {l : Lbl} :
      ProcStepₘ P l P' → l.i ∩ Q.f = ∅ →
      ProcStepₘ (P |ₚ Q) l (P' |ₚ Q)
  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStepₘ Q l Q' → l.i ∩ P.f = ∅ →
      ProcStepₘ (P |ₚ Q) l (P |ₚ Q')
  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStepₘ P l P' → ProcStepₘ Q l' Q' →
      (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  → (l |ₗ l').WF →
      ProcStepₘ (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')
  | one_bot
      {P P' : Proc} (L : Finset FPName)
      (hStep : ∀ x ∉ L, ∀ y ∉ L ∪ {x},
        ProcStepₘ P⸨#x, #y⸩ (x⟦⟧ |ₗ y⸨⸩) P') :
      ProcStepₘ (𝑣⸨•,•⸩ P) (τ) P'
  | tensor_parr
      {P P' : Proc} (L : Finset FPName)
      (hStep : ∀ x ∉ L, ∀ y ∉ L ∪ {x},
        ∀ x' ∉ L ∪ {x, y}, ∀ y' ∉ L ∪ {x, y, x'},
        ProcStepₘ P⸨#x, #y⸩ (x⟦x'⟧ |ₗ y⸨y'⸩) P'⸨2 | #x, #y⸩⸨#x', #y'⸩) :
      ProcStepₘ (𝑣⸨•,•⸩ P) (τ) (𝑣⸨•,•⸩ (𝑣⸨•,•⸩ P'))
  | res
      {P P' : Proc} {l : Lbl} (L : Finset FPName)
      (hStep : ∀ x y, x ∉ L → y ∉ L ∪ {x} →
        ProcStepₘ P⸨#x, #y⸩ l P'⸨#x, #y⸩) :
      ProcStepₘ (𝑣⸨•,•⸩ P) l (𝑣⸨•,•⸩ P')
