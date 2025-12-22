import PiLL.Framework.Process
import PiLL.Framework.Labels
import PiLL.Framwork.Alpha

def Proc.close (P : Proc) (names : List PName) : Proc :=
  match P with
  | .server x _ => names.foldr (fun n acc => Proc.dispose n acc) (x⟦⟧․𝟘)
  | _ => P

def Proc.open (P : Proc) (names : List PName) (σ : Renaming) : Proc :=
  match P with
  | .server _ _  => names.foldr (fun n acc => Proc.duplicate n (σ n) acc) ((rename σ P) |ₚ P)
  | _ => P

--------------------------- PROC-FUCNTION & TRANSITION RULES -------------------------

def proc {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : Proc := P

inductive ProcStep : (P : Proc) → Lbl → (P' : Proc) → Prop where
  | one
      {P : Proc} {x : PName} :
      ProcStep (x⟦⟧․P) (x⟦⟧) P

  | tensor
      {P : Proc} {x x' : PName} :
      ProcStep (x⟦x'⟧․P) (x⟦x'⟧) P

  | bot
      {P : Proc} {x : PName} :
      ProcStep (x⸨⸩․P) (x⸨⸩) P

  | parr
      {P : Proc} {x x' : PName} :
      ProcStep (x⸨x'⸩․P) (x⸨x'⸩) P

  | par₁
      {P P' Q : Proc} {l : Lbl} :
      ProcStep P l P' → l.i ∩ Q.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P' |ₚ Q)

  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStep Q l Q' → l.i ∩ P.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P |ₚ Q')

  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStep P l P' → ProcStep Q l' Q' →
      (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  → (l |ₗ l').WF →
      ---------------------------------------------
      ProcStep (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

  | alpha_equiv
      {P Q Q' : Proc} {l : Lbl} :
      (P =ₐ Q) → ProcStep Q l Q' →
      -------------------------------
      ProcStep P l Q'

  | one_bot
      {P P' : Proc} {x y : PName} :
      ProcStep P (x⟦⟧ |ₗ y⸨⸩) P' →
      ----------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) P'

  | tensor_parr
      {P P' : Proc} {x x' y y' : PName} :
      ProcStep P (x⟦x'⟧ |ₗ y⸨y'⸩) P' →
      -------------------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ (𝑣⸨x', y'⸩ P'))

  | res
      {P P' : Proc} {x y : PName} {l : Lbl} :
      ProcStep P l P' → l.fresh [x, y] →
      -------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (l) (𝑣⸨x, y⸩ P')

  | disp₁
      {P : Proc} {x : PName} :
      ProcStep (x⟦DISP⟧․P) (x⟦DISP⟧) (x⸨⸩․P)

  | disp₂
      {P : Proc} {x : PName} {names : List PName} :
      (P.f \ {x}).toList.mergeSort (· ≤ ·) = names →
      --------------------------------------------------
      ProcStep (!x․{P}) (x⸨DISP⸩) ((!x․{P}).close names)

  | dup₁
      {P : Proc} {x x' : PName} :
      ProcStep (x⟦DUP⟧⸨x'⸩․P) (x⟦DUP⟧) (x⸨x'⸩․P)

  | dup₂
      {P : Proc} {x x' : PName} {names : List PName} {σ : Renaming} :
      P.f ∩ (P.f.image σ) = ∅ → names = (P.f \ {x}).toList.mergeSort (· ≤ ·) →
      -------------------------------------------------------------------------
      ProcStep (!x․{P}) (x⸨DUP⸩) ((!x․{P}).open names σ)

  | use₁
      {P : Proc} {x : PName} :
      ProcStep (x⟦USE⟧․P) (x⟦USE⟧) P

  | use₂
      {P : Proc} {x : PName} :
      ProcStep (!x․{P}) (x⸨USE⸩) P

  | output
      {P : Proc} {x : PName} {A : Types} :
      ProcStep (x⟦A⟧․P) (x⟦A⟧) P

  | input
      {P : Proc} {x : PName} {A : Types} {X : TVar}:
      ProcStep (x⸨X⸩․P) (x⸨A⸩) (P{A // X})

  | selectL
      {P : Proc} {x : PName} :
      ProcStep (x⟦𝐋⟧․P) (x⟦𝐋⟧) P

  | ampL
      {P Q : Proc} {x : PName} :
      ProcStep (x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐋⸩) P

  | selectR
      {P : Proc} {x : PName} :
      ProcStep (x⟦𝐑⟧․P) (x⟦𝐑⟧) P

  | ampR
      {P Q : Proc} {x : PName} :
      ProcStep (x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐑⸩) Q

  | link₁
      {x y : PName} :
      ProcStep (x ⟷ₚ y) (x ⟷ₗ y) 𝟘

  | link₂
      {x y : PName} :
      ProcStep (x ⟷ₚ y) (y ⟷ₗ x) 𝟘

  | com {P P' : Proc} {x y : PName} {μ : Mu} :
      ProcStep P (x⟦μ⟧ |ₗ y⟦μ⟧) P' →
      -------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ P')

  | axcut
      {P P' : Proc} {x y z : PName} :
      ProcStep P (x ⟷ₗ y) P' →
      --------------------------------------
      ProcStep (𝑣⸨y, z⸩ P) (τ) (P'{x // z})

notation:50 P " -[" l "]->ₚ " P' => ProcStep P l P'

theorem ProcStep.preserves_WF (P P' : Proc) (l : Lbl) :
  ProcStep P l P' → l.WF := by
  intro h
  induction h <;> simp_all [Lbl.WF]

inductive MPST : (P : Proc) → Lbls → (P' : Proc) → Prop where
  | refl
    {P : Proc} :
    ------------
    MPST P (ε) P

  | stepR {l : Lbl} {ls : Lbls} {P P'' P' : Proc} :
    (MPST P ls P'') → (P'' -[l]->ₚ P') →
    ------------------------------------
          MPST P (ls ∷ₗ l) P'

notation:50 P " -[" ls "]->>ₚ " P' => MPST P ls P'
