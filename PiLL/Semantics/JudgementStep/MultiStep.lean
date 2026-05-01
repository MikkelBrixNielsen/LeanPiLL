import PiLL.Semantics.JudgementStep.Basic

inductive MTSTₘ : {n n' : Nat} → {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
  Typing n P 𝒢 → Lbls → Typing n' P' 𝒢' → Prop where
  | refl {n : Nat} {P : Proc} {𝒢 : HyperEnv} {𝒟 : Typing n P 𝒢} :
    MTSTₘ 𝒟 (ε) 𝒟
  | stepR {n n' n'' : Nat} {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
    (𝒟  : Typing n P 𝒢) (𝒟' : Typing n' P' 𝒢') (𝒟'' : Typing n'' P'' 𝒢'') :
    (MTSTₘ 𝒟 ls 𝒟'') → (𝒟'' -[l]-> 𝒟') →
    -------------------------------------
          MTSTₘ 𝒟 (ls ∷ₗ l) 𝒟'

instance {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} :
  HasMultiStep (Typing n P 𝒢) Lbls (Typing n' P' 𝒢') where
  step 𝒟 l 𝒟' := MTSTₘ 𝒟 l 𝒟'
