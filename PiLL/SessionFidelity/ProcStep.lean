import PiLL.Semantics.ProcStep.Basic
import PiLL.Semantics.JudgementStep.Basic

theorem session_fidelity_procₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟') :
  ProcStepₘ (proc 𝒟) l (proc 𝒟') := by
  induction hStep
  case one | bot => constructor
  case tensor Q _ y _ _ _ _ L ih hy =>
    have ⟨z, hz⟩ := exists_one_fresh (L ∪ {y})
    simp only [Finset.union_singleton, Finset.mem_insert, not_or, ← ne_eq] at hz
    obtain ⟨hzy, hz⟩ := hz
    have 𝒟y := Typing_tensor_all_fresh ih y hy
    have hfn := Typing_f_eq_names (ih z hz)
    have ⟨hnd, hpw⟩:= Typing_preserves_linearity 𝒟y
    have hD := HyperEnv.PairwiseDisjoint_implies_disjoint hpw
    simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, not_or,
      Finset.disjoint_insert_left, ← ne_eq] at hD
    simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
    obtain ⟨⟨hxy, hxΓ⟩, ⟨hyΔ, hDΓΔ⟩⟩ := hD
    obtain ⟨⟨hyΓ, hndΓ⟩, ⟨hxΔ, hndΔ⟩⟩ := hnd
    have h1 : y ∉ Q⸨#z⸩.f := by
      rw [hfn]
      simp only [List.cons_append, List.nil_append, HyperEnv.names_cons,
        Env.names_distributes, Finset.singleton_union, HyperEnv.names_nil,
        Finset.union_empty, Finset.union_insert, Finset.insert_union,
        Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq]
      exact ⟨hxy.symm, hzy.symm, hyΓ, hyΔ⟩
    have h2 := Proc.f_subset_open (P := Q) (x := z)
    apply ProcStepₘ.tensor
    simp only [Finset.singleton_union, Finset.mem_insert, not_or]
    constructor
    · exact hxy.symm
    · intro hy
      exact h1 ((Finset.subset_iff.mp h2) hy)
  case parr Q _ y _ _ _ _ L ih hy =>
    have ⟨z, hz⟩ := exists_one_fresh (L ∪ {y})
    simp only [Finset.union_singleton, Finset.mem_insert, not_or, ← ne_eq] at hz
    obtain ⟨hzy, hz⟩ := hz
    have 𝒟y := Typing_parr_all_fresh ih y hy
    have hfn := Typing_f_eq_names (ih z hz)
    have ⟨hnd, hpw⟩:= Typing_preserves_linearity 𝒟y
    simp only [HyperEnv.Nodup_singleton, Env.names_distributes, Env.Nodup_cons,
      Finset.notMem_union, Finset.notMem_singleton] at hnd
    obtain ⟨⟨hyx, hyΓ⟩, ⟨hxΓ, hndΓ⟩⟩ := hnd
    have h1 : y ∉ Q⸨#z⸩.f := by
      rw [hfn]
      simp only [HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
        HyperEnv.names_nil, Finset.union_empty, Finset.union_insert, Finset.mem_insert,
        not_or, ← ne_eq]
      exact ⟨hyx, hzy.symm, hyΓ⟩
    have h2 := Proc.f_subset_open (P := Q) (x := z)
    apply ProcStepₘ.parr
    simp only [Finset.singleton_union, Finset.mem_insert, not_or]
    constructor
    · exact hyx
    · intro hy
      exact h1 ((Finset.subset_iff.mp h2) hy)
  case par₁ hD ih | par₂ hD ih =>
    constructor
    · exact ih
    · exact hD
  case syn hD lwf ih1 ih2 => exact ProcStepₘ.syn ih1 ih2 hD lwf
  case one_bot ℋ Γ Q Q' m L huniq x y hx hy 𝒟'' hSP ih =>
    simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Finset.mem_union, not_or, ← ne_eq] at hx hy
    obtain ⟨hxy, hxQf, hxℋ, hxΓ⟩ := hx
    obtain ⟨hyQf, hyℋ, hyΓ⟩ := hy
    exact ProcStepₘ.one_bot hxQf hyQf hxy ih
  case tensor_parr ih =>
    expose_names
    simp only [proc] at ⊢ ih
    apply ProcStepₘ.tensor_parr hxP hyP hx'P hy'P hxP' hyP' hx'P' hy'P'
      hxx' hneq hxy' hyx' hyy' hneq' ih
  case res ih =>
    expose_names
    simp only [Finset.union_assoc, Finset.mem_union, not_or] at hx_pre hx_post hy_pre hy_post
    have h1 : x ∉ P_1.f ∪ P'_1.f := by simp [hx_pre, hx_post]
    have h2 : y ∉ P_1.f ∪ P'_1.f := by simp [hy_pre, hy_post]
    exact ProcStepₘ.res hneq h1 h2 hlx hly ih
  case perm_hyper ih | perm_env ih => exact ih
