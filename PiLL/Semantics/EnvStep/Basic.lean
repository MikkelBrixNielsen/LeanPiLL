import PiLL.Model.HyperEnvironment.Basic
import PiLL.Model.STypes.Notation
import PiLL.Semantics.Labels

inductive EnvStepₘ : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : FPName} :
      EnvStepₘ [[x ∶ 1]] (x⟦⟧) ∅
  | tensor
      {Γ Δ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ]) :
      EnvStepₘ [x ∶ A ⨂ B :: Γ‚ Δ] (x⟦x'⟧) ([x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ])
  | bot
      {Γ : Env} {x : FPName} :
      EnvStepₘ [x ∶ ⊥ :: Γ] (x⸨⸩) [Γ]
  | parr
      {Γ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⅋ B :: Γ]) :
      EnvStepₘ [x ∶ A ⅋ B :: Γ] (x⸨x'⸩) [x' ∶ A :: x ∶ B :: Γ]
  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStepₘ 𝒢 l 𝒢' →
      -----------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)
  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStepₘ ℋ l ℋ' →
      -----------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')
  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStepₘ 𝒢 l 𝒢' → EnvStepₘ ℋ l' ℋ' →
      --------------------------------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')
  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
      EnvStepₘ (𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ [Γ]) →
      ---------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ]) (τ) (𝒢 |ₕ [Γ])
  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': FPName} {A B : Types} :
      EnvStepₘ
        (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ]) →
      ------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ‚ Ξ]) (τ) (𝒢 |ₕ [Γ‚ Δ‚ Ξ])
  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A : Types} {l : Lbl}
      (hFx : x ∉ l.i ∪ l.f) (hFy : y ∉ l.i ∪ l.f) :
      EnvStepₘ (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) (l) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])
  ------- Additional Structural / Exchange Rules -------
  | perm_env {𝒢 ℋ : HyperEnv} {Γ Γ' : Env} {l : Lbl} (hP1 : Γ ~ Γ') :
      (hES : EnvStepₘ (Γ :: 𝒢) l ℋ) →
      ---------------------------------
      EnvStepₘ (Γ' :: 𝒢) l ℋ
  | perm_hyper {𝒢 𝒢' ℋ ℋ' : HyperEnv} {l : Lbl} (hP1 : 𝒢 ~ 𝒢') (hP2 : ℋ ~ ℋ') :
      (hES : EnvStepₘ 𝒢 l ℋ) →
      -------------------------
      EnvStepₘ 𝒢' l ℋ'

instance : HasStep HyperEnv Lbl HyperEnv where step := EnvStepₘ
