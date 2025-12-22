import PiLL.Framework.Judgement
import PiLL.Framwork.Labels

------------------------- ENV-FUCNTION & TRANSITION RULES --------------------------

def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : PName} :
      EnvStep (x ∶ 1) (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep (Γ‚ Δ‚ x ∶ A ⨂ B) (x⟦x'⟧) (Γ‚ x'∶ A |ₕ Δ‚ x ∶ B)

  | bot
      {Γ : Env} {x : PName} :
      EnvStep (Γ‚ x ∶ ⊥) (x⸨⸩) Γ

  | parr
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⅋ B) (x⸨x'⸩) (Γ‚ x' ∶ A‚ Δ‚ x ∶ B)

  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStep 𝒢 l 𝒢' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStep ℋ l ℋ' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStep 𝒢 l 𝒢' → EnvStep ℋ l' ℋ' → (l |ₗ l').WF →
      --------------------------------------------------
      EnvStep (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')

  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {x y : PName} :
      EnvStep (𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ Γ) →
      ------------------------------------------------------
      EnvStep (𝒢 |ₕ Γ) (τ) (𝒢 |ₕ Γ)

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': PName} {A B : Types} :
      EnvStep
        (𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ)
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B |ₕ Ξ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) →
      ---------------------------------------------------
      EnvStep (𝒢 |ₕ Γ‚ Δ‚ Ξ) (τ) (𝒢 |ₕ Γ‚ Δ‚ Ξ)

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : PName} {A B : Types} {l : Lbl} :
      EnvStep (𝒢 |ₕ Γ‚ x ∶ Aᗮ |ₕ Δ‚ y ∶ A) (l) (𝒢' |ₕ Γ'‚ x ∶ Aᗮ |ₕ Δ'‚ y ∶ A) →
      ----------------------------------------------------------------------------
      EnvStep (𝒢 |ₕ Γ‚ Δ) l (𝒢' |ₕ Γ'‚ Δ')

  | selectL
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧) (Γ‚ x ∶ A)

  | ampL
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A & B) (x⸨𝐋⸩) (Γ‚ x ∶ A)

  | selectR
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧) (Γ‚ x ∶ B)

  | ampR
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A & B) (x⸨𝐑⸩) (Γ‚ x ∶ B)

  | link₁
      {x y : PName} {A : Types} :
      EnvStep (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₗ y) ∅

  | link₂ -- FIXME this one isn't actually in the definition in Fig 8, but it matches ProcStep
      {x y : PName} {A : Types} :
      EnvStep (x ∶ Aᗮ‚ y ∶ A) (y ⟷ₗ x) ∅

  | use₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ??A) (x⟦USE⟧) (Γ‚ x ∶ A)

  | use₂
      {Γ : Env} {x : PName} {A : Types} :
      ?ₑΓ →
      --------------------------------------
      EnvStep (Γ‚ x ∶ !!A) (x⸨USE⸩) (Γ‚ x ∶ A)

  | disp₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ??A) (x⟦DISP⟧) (Γ‚ x ∶ ⊥)

  | disp₂
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep {Γ‚ x ∶ !!A} (x⸨DISP⸩) (Γ‚ x ∶ 1)

  | dup₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ??A) (x⟦DUP⟧) (Γ‚ x ∶ ??A ⅋ ??A)

  | dup₂
      {Γ : Env} {x : PName} {A : Types} :
      ?ₑΓ →
      ----------------------------------------------
      EnvStep (Γ‚ x ∶ !!A) (x⸨DUP⸩) (Γ‚ x ∶ !!A ⨂ !!A)

  | output
      {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
      EnvStep (Γ‚ x ∶ ∃X․B) (x⟦A⟧) (Γ‚ x ∶ B{A // X})

  | input
      {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
      EnvStep (Γ‚ x ∶ ∀X․B) (x⸨A⸩) (Γ‚ x ∶ B{A // X})

notation:50 P " -[" l "]->ₑ " P' => EnvStep P l P'

theorem EnvStep.preserves_WF (Γ Γ' : HyperEnv) (l : Lbl) :
  EnvStep Γ l Γ' → l.WF := by
  intro h
  induction h <;> simp_all [Lbl.WF]

inductive MEST : (𝒢 : HyperEnv) → Lbls → (𝒢' : HyperEnv) → Prop where
  | refl
    {𝒢 : HyperEnv} :
    -------------
    MEST 𝒢 (ε) 𝒢

  | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢'' 𝒢' : HyperEnv} :
    (MEST 𝒢 ls 𝒢'') → (𝒢'' -[l]->ₑ 𝒢') →
    ------------------------------------
          MEST 𝒢 (ls ∷ₗ l) 𝒢'

notation:50 𝒢 " -[" ls "]->>ₑ " 𝒢' => MPST 𝒢 ls 𝒢'
