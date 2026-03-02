import PiLL.Framework.Model.Judgement
import PiLL.Framework.Semantics.Labels

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : FPName} :
      EnvStep [[x ∶ 1]] (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : FPName} {A B : Types} :
      EnvStep [x ∶ A ⨂ B :: Γ‚ Δ] (x⟦x'⟧) ([x'∶ A :: Γ] |ₕ [x ∶ B :: Δ])

  | bot
      {Γ : Env} {x : FPName} :
      EnvStep [x ∶ ⊥ :: Γ] (x⸨⸩) [Γ]

  | parr
      {Γ : Env} {x x' : FPName} {A B : Types} :
      EnvStep [x ∶ A ⅋ B :: Γ] (x⸨x'⸩) [x ∶ B :: x' ∶ A :: Γ]

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
      {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
      EnvStep (𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ [Γ]) →
      ---------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ]) (τ) (𝒢 |ₕ [Γ])

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': FPName} {A B : Types} :
      EnvStep
        (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ [x' ∶ A :: Γ] |ₕ [x' ∶ A :: Δ] |ₕ [y ∶ Bᗮ :: y' ∶ Aᗮ :: Ξ]) →
      ------------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ‚ Δ‚ Ξ]) (τ) (𝒢 |ₕ [Γ‚ Δ‚ Ξ])

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A B : Types} {l : Lbl} :
      EnvStep (𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]) (l) (𝒢' |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])

  | selectL
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A ⊕ B :: Γ] (x⟦𝐋⟧) [x ∶ A :: Γ]

  | ampL
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A & B :: Γ] (x⸨𝐋⸩) [x ∶ A :: Γ]

  | selectR
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A ⊕ B :: Γ] (x⟦𝐑⟧) [x ∶ B :: Γ]

  | ampR
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A & B :: Γ] (x⸨𝐑⸩) [x ∶ B :: Γ]

  | link₁
      {x y : FPName} {A : Types} :
      EnvStep [x ∶ Aᗮ :: [y ∶ A]] (x ⟷ₗ y) ∅

  | use₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A :: Γ] (x⟦USE⟧) [x ∶ A :: Γ]

  | use₂
      {Γ : Env} {x : FPName} {A : Types} :
      ?ₑΓ →
      -------------------------------------------
      EnvStep [x ∶ !!A :: Γ] (x⸨USE⸩) [x ∶ A :: Γ]

  | disp₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A :: Γ] (x⟦DISP⟧) [x ∶ ⊥ :: Γ]

  | disp₂
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ !!A :: Γ] (x⸨DISP⸩) [x ∶ 1 :: Γ]

  | dup₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A:: Γ] (x⟦DUP⟧) [x ∶ ??A ⅋ ??A :: Γ]

  | dup₂
      {Γ : Env} {x : FPName} {A : Types} :
      ?ₑΓ →
      ---------------------------------------------------
      EnvStep [x ∶ !!A :: Γ] (x⸨DUP⸩) [x ∶ !!A ⨂ !!A :: Γ]

  | output
      {Γ : Env} {x : FPName} {A B : Types} {X : TVar} :
      EnvStep [x ∶ ∃․B :: Γ] (x⟦A⟧) [x ∶ B{A // 0} :: Γ]

  | input
      {Γ : Env} {x : FPName} {A B : Types} {X : TVar} :
      EnvStep [x ∶ ∀․B :: Γ] (x⸨A⸩) [x ∶ B{A // 0} :: Γ]

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

notation:50 𝒢 " -[" ls "]->>ₑ " 𝒢' => MEST 𝒢 ls 𝒢'
