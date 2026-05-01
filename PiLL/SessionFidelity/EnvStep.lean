import PiLL.Semantics.EnvStep.Basic
import PiLL.Semantics.JudgementStep.Basic

-- env: Der → Env (HyperEnv)
theorem session_fidelity_envₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟') :
  EnvStepₘ (env 𝒟) l (env 𝒟') := by
  induction hStep
  case one | bot => constructor
  case tensor y _ _ _ _ L 𝒟' hy =>
    have ⟨z, hz⟩ := exists_one_fresh L
    have 𝒟y := Typing_tensor_all_fresh 𝒟' y hy
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟y
    have hD := HyperEnv.PairwiseDisjoint_implies_disjoint hpw
    simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, not_or,
      Finset.disjoint_insert_left, ← ne_eq] at hD
    simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
    obtain ⟨⟨hxy, hxΓ⟩, hyΔ, hDΓΔ⟩ := hD
    obtain ⟨⟨hyΓ, hndΓ⟩, ⟨hxΔ, hndΔ⟩⟩ := hnd
    apply EnvStepₘ.tensor
    simp only [HyperEnv.names_distributes, Env.names_distributes, Finset.notMem_union,
      Finset.notMem_singleton, Env.names_merge, HyperEnv.names_nil]
    split_ands
    · exact hxy.symm
    · exact hyΓ
    · exact hyΔ
    · simp only [Finset.notMem_empty, not_false_eq_true]
  case parr y _ _ _ _ L 𝒟' hy =>
    have ⟨z, hz⟩ := exists_one_fresh L
    have 𝒟y := Typing_parr_all_fresh 𝒟' y hy
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟y
    simp only [HyperEnv.Nodup_singleton, Env.names_distributes, Env.Nodup_cons,
      Finset.notMem_union, Finset.notMem_singleton] at hnd
    apply EnvStepₘ.parr
    simp only [HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty, Finset.mem_insert, not_or, hnd.1,
      not_false_eq_true, true_and]
  case par₁ ih | par₂ ih =>
    constructor
    exact ih
  case syn ih1 ih2 => exact EnvStepₘ.syn ih1 ih2
  case one_bot ih =>
    exact EnvStepₘ.one_bot ih
  case tensor_parr ih =>
    simp only [env] at ⊢ ih
    rw [← Env.merge_assoc]
    exact EnvStepₘ.tensor_parr ih
  case res hlx hly _ ih =>
    apply EnvStepₘ.res ?_ ?_ ih
    all_goals
      simp only [Finset.mem_union, not_or] at hlx hly ⊢
    · exact ⟨hlx.2, hlx.1⟩
    · exact ⟨hly.2, hly.1⟩
  case perm_hyper hP hP' hTS ih => exact EnvStepₘ.perm_hyper hP hP' ih
  case perm_env hP hTS ih => exact EnvStepₘ.perm_env hP ih
