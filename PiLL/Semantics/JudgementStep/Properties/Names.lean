import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic

lemma TypingStepₘ_names_bound {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv} {l : Lbl}
  {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 l 𝒟') :
  𝒢'.names ⊆ 𝒢.names ∪ l.i := by
  induction hStep
  case one =>
    simp only [List.empty_eq, HyperEnv.names_nil, HyperEnv.names_cons, Env.names_distributes,
      Env.names_nil, Finset.union_empty, Lbl.i, iNamesAct, Finset.subset_singleton_iff,
      Finset.empty_ne_singleton, or_false]
  case bot =>
    simp only [HyperEnv.names_cons, HyperEnv.names_nil, Finset.union_empty, Env.names_distributes,
      Finset.singleton_union, Lbl.i, iNamesAct, Finset.subset_insert]
  case tensor Γ Δ _ x y _ _ _ _ _ _ _ =>
    simp only [HyperEnv.names_merge, HyperEnv.names_singleton,
      Env.names_distributes, Lbl.i, iNamesAct, Env.names_merge]
    rw [Finset.union_comm, Finset.union_assoc, Finset.union_comm _ Γ.names,
      ← Finset.union_assoc Δ.names _, Finset.union_comm Δ.names Γ.names]
    simp only [← Finset.union_assoc, subset_refl]
  case parr =>
    simp only [HyperEnv.names_singleton, Env.names_distributes, Lbl.i, iNamesAct]
    rw [Finset.union_comm]
  case tensor_parr | one_bot =>
    simp only [HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge, HyperEnv.names_nil,
      Finset.union_empty, List.append_assoc, Lbl.i, subset_refl]
  case par₁ ih =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢' | hyℋ
    · have := ih hy𝒢'
      simp only [Finset.mem_union] at this
      rcases this with h1 | h2
      · simp only [h1, true_or, Lbl.i, iNamesAct]
      · simp only [h2, or_true]
    · simp only [hyℋ, or_true, Lbl.i, iNamesAct, true_or]
  case par₂ ih =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢 | hyℋ'
    · simp only [hy𝒢, true_or, Lbl.i, iNamesAct]
    · have := ih hyℋ'
      simp only [Finset.mem_union] at this
      rcases this with h1 | h2
      · simp only [h1, or_true, Lbl.i, iNamesAct, true_or]
      · simp only [h2, or_true]
  case syn ih1 ih2 =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢' | hyℋ'
    · have := ih1 hy𝒢'
      simp only [Finset.mem_union] at this
      rcases this with h1 | h2
      · simp only [h1, true_or, Lbl.i, iNamesAct, Finset.mem_union]
      · simp only [Lbl.i_par', Finset.mem_union, h2, true_or, or_true]
    · have := ih2 hyℋ'
      simp only [Finset.mem_union] at this
      rcases this with h1 | h2
      · simp only [h1, or_true, Lbl.i, iNamesAct, Finset.mem_union, true_or]
      · simp only [Lbl.i_par', Finset.mem_union, h2, or_true]
  case res 𝒢' _ Γ' _ Δ' _ _ A _ _ _ _ _ huniq' x y hneq hx hy hx' hy' hlx hly hStep ih =>
    intro a ha
    simp only [HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge, HyperEnv.names_nil,
      Finset.union_empty, Finset.mem_union, List.append_assoc, List.cons_append,
      List.nil_append, Env.names_distributes, Finset.singleton_union, Finset.union_insert,
      Finset.insert_union, Finset.union_assoc] at ha ih ⊢
    have haLHS : a ∈ insert y (insert x (𝒢'.names ∪ (Γ'.names ∪ Δ'.names))) := by
      simp only [Finset.mem_insert, Finset.mem_union, ha, or_true]
    have haRHS := ih haLHS
    simp only [Finset.mem_insert, Finset.mem_union] at haRHS
    simp only [Finset.notMem_union, and_assoc] at hx hy hx' hy'
    obtain ⟨hxPf', hx𝒢', hxΓ', hxΔ'⟩ := hx'
    obtain ⟨hyPf', hy𝒢', hyΓ', hyΔ'⟩ := hy'
    rcases haRHS with rfl | rfl | h
    · rcases ha with h1 | h2 | h3
      · exfalso ; apply hy𝒢' h1
      · exfalso ; apply hyΓ' h2
      · exfalso ; apply hyΔ' h3
    · rcases ha with h1 | h2 | h3
      · exfalso ; apply hx𝒢' h1
      · exfalso ; apply hxΓ' h2
      · exfalso ; apply hxΔ' h3
    · exact h
  case perm_hyper hP hP' _ ih =>
    rw [← (HyperEnv.names_eq_of_perm hP), ← (HyperEnv.names_eq_of_perm hP')]
    exact ih
  case perm_env hP _ ih =>
    simp only [HyperEnv.names_cons, Finset.union_assoc] at ⊢ ih
    rw [← (Env.names_eq_of_perm hP)]
    exact ih
