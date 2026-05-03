import PiLL.Semantics.JudgementStep.Basic
import PiLL.Semantics.JudgementStep.Properties.Names
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.Judgement.Properties.Linearity

-- FIXME: Move to hyperenvironments
lemma HyperEnv.Perm.length_eq {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  𝒢.length = ℋ.length := by
  induction hP with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma HyperEnv.Perm_merge_inv_one {𝒢 ℋ 𝒥 : HyperEnv} {Γ : Env}
  (hP : 𝒢 |ₕ ℋ ~ 𝒥 |ₕ [Γ]) :
  (∃ 𝒢ᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [Γ] ∧ 𝒥 ~ 𝒢ᵣ |ₕ ℋ) ∨
  (∃ ℋᵣ, ℋ ~ ℋᵣ |ₕ [Γ] ∧ 𝒥 ~ 𝒢 |ₕ ℋᵣ) := by
  have h_in_RHS : Γ ∈ 𝒥 |ₕ [Γ] := by simp
  have ⟨Γ', h_in_LHS, hΓ'⟩ := HyperEnv.Perm_mem hP h_in_RHS
  simp only [List.mem_append] at h_in_LHS
  rcases h_in_LHS with h_in_G | h_in_H
  · left
    obtain ⟨𝒢_rest, hG_ext⟩ := HyperEnv.exists_perm_cons_of_mem h_in_G
    have h1 : Γ' :: 𝒢_rest ~ [Γ'] |ₕ 𝒢_rest := by
      simp only [List.cons_append, List.nil_append, Perm_refl]
    have h2 := (HyperEnv.Perm.exchange_rhs_left
      (HyperEnv.Perm_singleton_singleton.mpr hΓ')
      (hG_ext.trans h1)).trans HyperEnv.Perm.merge_comm
    have h3 := HyperEnv.Perm.exchange_rhs_left h2 hP.symm
    apply HyperEnv.Perm_rotate_rhs_left at h3
    apply HyperEnv.Perm_merge_cancel_right at h3
    refine ⟨𝒢_rest, h2, h3.trans HyperEnv.Perm.merge_comm⟩
  · right
    obtain ⟨ℋ_rest, hH_ext⟩ := HyperEnv.exists_perm_cons_of_mem h_in_H
    have h1 : Γ' :: ℋ_rest ~ [Γ'] |ₕ ℋ_rest := by
      simp only [List.cons_append, List.nil_append, Perm_refl]
    have h2 := (HyperEnv.Perm.exchange_rhs_left
      (HyperEnv.Perm_singleton_singleton.mpr hΓ')
      (hH_ext.trans h1)).trans HyperEnv.Perm.merge_comm
    have h3 := HyperEnv.Perm.exchange_rhs_left h2
      (hP.symm.trans HyperEnv.Perm.merge_comm)
    apply HyperEnv.Perm_rotate_rhs_left at h3
    apply HyperEnv.Perm_merge_cancel_right at h3
    refine ⟨ℋ_rest, h2, h3⟩

lemma HyperEnv.Perm_merge_inv_two_blocks {𝒢 ℋ 𝒥 : HyperEnv} {Γ Δ : Env}
  (hP : 𝒢 |ₕ ℋ ~ 𝒥 |ₕ [Γ] |ₕ [Δ]) :
  (∃ 𝒢ᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [Γ] |ₕ [Δ] ∧ 𝒥 ~ 𝒢ᵣ |ₕ ℋ) ∨
  (∃ ℋᵣ, ℋ ~ ℋᵣ |ₕ [Γ] |ₕ [Δ] ∧ 𝒥 ~ 𝒢 |ₕ ℋᵣ) ∨
  (∃ 𝒢ᵣ ℋᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [Γ] ∧ ℋ ~ ℋᵣ |ₕ [Δ] ∧ 𝒥 ~ 𝒢ᵣ |ₕ ℋᵣ) ∨
  (∃ 𝒢ᵣ ℋᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [Δ] ∧ ℋ ~ ℋᵣ |ₕ [Γ] ∧ 𝒥 ~ 𝒢ᵣ |ₕ ℋᵣ) := by
  have h_split1 := HyperEnv.Perm_merge_inv_one hP
  rcases h_split1 with ⟨𝒢_rest1, hG1, hJ1⟩ | ⟨ℋ_rest1, hH1, hJ1⟩
  · have h_split2 := HyperEnv.Perm_merge_inv_one hJ1.symm
    rcases h_split2 with ⟨𝒢_rest2, hG2, hJ2⟩ | ⟨ℋ_rest2, hH2, hJ2⟩
    · left
      exact ⟨𝒢_rest2, HyperEnv.Perm.exchange_rhs_left hG2 hG1, hJ2⟩
    · right ; right ; right
      exact ⟨𝒢_rest1, ℋ_rest2, hG1, hH2, hJ2⟩
  · have h_split2 := HyperEnv.Perm_merge_inv_one hJ1.symm
    rcases h_split2 with ⟨𝒢_rest2, hG2, hJ2⟩ | ⟨ℋ_rest2, hH2, hJ2⟩
    · right; right; left ; exact ⟨𝒢_rest2, ℋ_rest1,hG2, hH1, hJ2⟩
    · right ; left ; exact ⟨ℋ_rest2, HyperEnv.Perm.exchange_rhs_left hH2 hH1, hJ2⟩

-- FIXME: Move to own file in properties
lemma TypingStepₘ_preserves_block {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv} {l : Lbl}
  {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟')
  {Γ : Env} (hΓ : Γ ∈ 𝒢) (hD : Disjoint Γ.names (l.f ∪ l.i)) :
  ∃ Γ' ∈ 𝒢', Γ' ~ Γ := by
  induction hStep generalizing Γ
  case one | bot | tensor | parr =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hΓ
    subst hΓ
    simp only [Env.names_distributes, Env.names_merge, Finset.singleton_union, Lbl.f, fNamesAct,
      Lbl.i, iNamesAct, Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_union,
      Env.mem_pair_fst_in_names_iff, true_or, not_true_eq_false, Finset.disjoint_singleton_right,
      not_or, not_exists, false_and] at hD
  case par₁ ih =>
    simp only [List.mem_append] at hΓ ⊢
    · rcases hΓ with h1 | h2
      · have ⟨Ξ, hΞ, hPΞ⟩ := ih h1 hD
        use Ξ
        exact ⟨Or.inl hΞ, hPΞ⟩
      · use Γ
        exact ⟨Or.inr h2, by rfl⟩
  case par₂ ih =>
    simp only [List.mem_append] at hΓ ⊢
    · rcases hΓ with h1 | h2
      · use Γ
        exact ⟨Or.inl h1, by rfl⟩
      · have ⟨Ξ, hΞ, hPΞ⟩ := ih h2 hD
        use Ξ
        exact ⟨Or.inr hΞ, hPΞ⟩
  case syn ih1 ih2 =>
    simp only [List.mem_append] at hΓ ⊢
    rcases hΓ with h1 | h2
    · have ⟨Ξ, hΞ, hPΞ⟩ := ih1 h1 ?_
      · use Ξ
        exact ⟨Or.inl hΞ, hPΞ⟩
      · simp_all only [HyperEnv.disjoint, Lbl.i, iNamesAct, Proc.f_par, Lbl.WF, Lbl.f, fNamesAct,
        Finset.disjoint_union_right, and_imp, Finset.union_assoc, and_self]
    · have ⟨Ξ, hΞ, hPΞ⟩ := ih2 h2 ?_
      · use Ξ
        exact ⟨Or.inr hΞ, hPΞ⟩
      · simp_all only [HyperEnv.disjoint, Lbl.i, iNamesAct, Proc.f_par, Lbl.WF, Lbl.f, fNamesAct,
        Finset.disjoint_union_right, and_imp, Finset.union_assoc, and_self]
  case one_bot => use Γ
  case tensor_parr => use Γ ; rw [← Env.merge_assoc] ; exact ⟨hΓ, by rfl⟩
  case res =>
    expose_names
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hΓ
    rcases hΓ with h1 | h2
    · have hΓ': Γ ∈ 𝒢_1 |ₕ [x ∶ A :: Γ_1] |ₕ [y ∶ Aᗮ :: Δ] := by
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
        left ; exact h1
      obtain ⟨Γ'_post, h_post_in, h_post_perm⟩ := hStep_ih hΓ' hD
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at h_post_in
      rcases h_post_in with hin | rfl | rfl
      · use Γ'_post
        refine ⟨?_, h_post_perm⟩
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] ; left ; exact hin
      · exfalso
        have hΓ := (List.Perm.mem_iff (a := x ∶ A) h_post_perm).mp (by simp)
        simp only [Finset.union_assoc, Finset.mem_union, Env.mem_pair_fst_in_names_iff, not_or,
          not_exists] at hx_pre
        apply hx_pre.2.1 (HyperEnv.mem_of_mem_mem_names hΓ h1)
      · exfalso
        have hΓ := (List.Perm.mem_iff (a := y ∶ Aᗮ) h_post_perm).mp (by simp)
        simp only [Finset.union_assoc, Finset.mem_union, Env.mem_pair_fst_in_names_iff, not_or,
          not_exists] at hy_pre
        apply hy_pre.2.1 (HyperEnv.mem_of_mem_mem_names hΓ h1)
    · subst h2
      use (Γ'‚ Δ')
      refine ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
      · have h_x_pre : x ∶ A :: Γ_1 ∈ 𝒢_1 |ₕ [x ∶ A :: Γ_1] |ₕ [y ∶ Aᗮ :: Δ] := by simp
        have h_x_disj : Disjoint (Env.names (x ∶ A :: Γ_1)) (l_1.f ∪ l_1.i) := by
          simp only [Env.names_distributes]
          rw [Finset.disjoint_union_left, Finset.disjoint_singleton_left]
          refine ⟨hlx, ?_⟩
          simp only [Env.names_merge, Finset.disjoint_union_left] at hD
          exact hD.1
        obtain ⟨x_post, h_x_post_in, h_x_perm⟩ := hStep_ih h_x_pre h_x_disj
        have h_x_block_eq : x_post = x ∶ A :: Γ' := by
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false] at h_x_post_in
          have hx_in_x_post := (List.Perm.mem_iff (a := x ∶ A) h_x_perm).mpr (by simp)
          rcases h_x_post_in with hin | rfl | rfl
          · have hx_in_G'_1 := HyperEnv.mem_of_mem_mem_names hx_in_x_post hin
            have h_contra : x ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
              simp [hx_in_G'_1]
            exact False.elim (hx_post h_contra)
          · rfl
          · exfalso
            simp only [List.mem_cons, Prod.mk.injEq] at hx_in_x_post
            rcases hx_in_x_post with ⟨rfl, _⟩ | hΔ
            · exact hneq (by rfl)
            · have h_contra : x ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
                simp only [Finset.union_assoc, Finset.mem_union]
                right ; right ; right ; exact Env.mem_pair_fst_in_names _ hΔ
              exact (hx_post h_contra)
        subst h_x_block_eq
        have h_y_pre : y ∶ Aᗮ :: Δ ∈ 𝒢_1 |ₕ [x ∶ A :: Γ_1] |ₕ [y ∶ Aᗮ :: Δ] := by simp
        have h_y_disj : Disjoint (Env.names (y ∶ Aᗮ :: Δ)) (l_1.f ∪ l_1.i) := by
          simp only [Env.names_distributes]
          rw [Finset.disjoint_union_left, Finset.disjoint_singleton_left]
          refine ⟨hly, ?_⟩
          simp only [Env.names_merge, Finset.disjoint_union_left] at hD
          exact hD.2
        obtain ⟨y_post, h_y_post_in, h_y_perm⟩ := hStep_ih h_y_pre h_y_disj
        have h_y_block_eq : y_post = y ∶ Aᗮ :: Δ' := by
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false] at h_y_post_in
          have hy_in_y_post := (List.Perm.mem_iff (a := y ∶ Aᗮ) h_y_perm).mpr (by simp)
          rcases h_y_post_in with hin | rfl | rfl
          · have hy_in_G'_1 := HyperEnv.mem_of_mem_mem_names hy_in_y_post hin
            have h_contra : y ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
              simp [hy_in_G'_1]
            exact False.elim (hy_post h_contra)
          · exfalso
            simp only [List.mem_cons, Prod.mk.injEq] at hy_in_y_post
            rcases hy_in_y_post with ⟨rfl, _⟩ | hΓ
            · exact hneq (by rfl)
            · have h_contra : y ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
                simp only [Finset.union_assoc, Finset.mem_union]
                right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΓ
              exact (hy_post h_contra)
          · rfl
        subst h_y_block_eq
        exact List.Perm.append
          (List.Perm.cons_inv h_x_perm)
          (List.Perm.cons_inv h_y_perm)
  case perm_env ℋ Γ Γ' _ _ _ _ _ _ _ _ hP _ ih =>
    expose_names
    simp only [List.mem_cons] at hΓ
    rcases hΓ with rfl | h_in_H
    · have h_pre_in : Γ' ∈ Γ' :: ℋ := by simp
      have hNames := Env.names_eq_of_perm hP
      have hD_pre : Disjoint Γ'.names (l_1.f ∪ l_1.i) := by
        rw [hNames]
        exact hD
      obtain ⟨Γ_post, h_post_in, h_post_perm⟩ := ih h_pre_in hD_pre
      use Γ_post, h_post_in
      exact h_post_perm.trans hP
    · have h_pre_in : Γ ∈ Γ' :: ℋ := List.mem_cons_of_mem _ h_in_H
      obtain ⟨Γ_post, h_post_in, h_post_perm⟩ := ih h_pre_in hD
      use Γ_post, h_post_in
  case perm_hyper =>
    expose_names
    obtain ⟨Γ_pre, h_pre_in, h_pre_perm⟩ := HyperEnv.Perm_mem hP1 hΓ
    have hNames_pre := Env.names_eq_of_perm h_pre_perm
    have hD_pre : Disjoint Γ_pre.names (l_1.f ∪ l_1.i) := by
      rw [hNames_pre]
      exact hD
    obtain ⟨Γ_post, h_post_in, h_post_perm⟩ := hTS_ih h_pre_in hD_pre
    obtain ⟨Γ_final, h_final_in, h_final_perm⟩ := HyperEnv.Perm_mem hP2.symm h_post_in
    use Γ_final, h_final_in
    exact h_final_perm.trans (h_post_perm.trans h_pre_perm)

lemma TypingStepₘ_f_names_subset {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv} {l : Lbl}
  {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟') :   l.f ⊆ 𝒢.names := by
  induction hStep
  case one => simp
  case bot => simp
  case tensor => simp
  case parr => simp
  case par₁ ih =>
    expose_names
    simp only [HyperEnv.names_merge]
    exact ih.trans (Finset.subset_union_left (s₂ := ℋ.names))
  case par₂ ih =>
    expose_names
    simp only [HyperEnv.names_merge]
    exact ih.trans (Finset.subset_union_right (s₂ := ℋ.names))
  case syn lwf ih1 ih2=>
    simp only [HyperEnv.names_merge, Lbl.f_par', Lbl.WF] at ⊢ lwf
    exact Finset.union_subset_union ih1 ih2
  case one_bot => simp
  case tensor_parr => simp
  case res =>
    expose_names
    simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Env.names_distributes,
      ← Finset.union_assoc, Env.names_merge] at hStep_ih ⊢
    simp only [Finset.notMem_union] at hlx hly
    intros z hz
    have h_mem := hStep_ih hz
    simp only [Finset.mem_union, Finset.mem_singleton, or_assoc] at h_mem
    rcases h_mem with hG | rfl | hΓ | rfl | hΔ
    · simp only [Finset.mem_union] ; left ; left ; exact hG
    · exfalso; exact hlx.1 hz
    · simp only [Finset.mem_union] ; left ; right ; exact hΓ
    · exfalso; exact hly.1 hz
    · simp only [Finset.mem_union] ; right ; exact hΔ
  case perm_env hP _ ih =>
    simp only [HyperEnv.names_distributes]
    rw [← Env.names_eq_of_perm hP]
    exact ih
  case perm_hyper hP _ _ ih =>
    rw [← HyperEnv.names_eq_of_perm hP]
    exact ih


























lemma TypingStepₘ_preserves_single_block {n n' : Nat} {P P' : Proc}
  {𝒢 ℋ : HyperEnv} {l : Lbl} {𝒟' : n' ⊢ P' ∷ ℋ}
  {𝒢' : HyperEnv} {Γ : Env} {A : Types} {x : FPName}
  (𝒟 : n ⊢ P ∷ 𝒢) (hStep : TypingStepₘ 𝒟 l 𝒟')
  (hxl : x ∉ l.f ∪ l.i)
  (hP : 𝒢 ~ 𝒢' |ₕ [x ∶ A :: Γ]) :
  ∃ 𝒢' Γ', ℋ ~ 𝒢' |ₕ [x ∶ A :: Γ'] := by
  induction hStep generalizing 𝒢' Γ
  case one =>
    expose_names
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_cons, List.length_nil, zero_add, List.length_append,
      Nat.right_eq_add, List.length_eq_zero_iff, Lbl.f, fNamesAct, Lbl.i, iNamesAct,
      Finset.union_empty, Finset.mem_singleton] at h_len hxl
    subst h_len
    rw [HyperEnv.merge_nilL] at hP
    have h_len := List.Perm.length_eq (HyperEnv.Perm_singleton_singleton.mp hP)
    simp only [List.length_cons, List.length_nil, zero_add, Nat.right_eq_add,
      List.length_eq_zero_iff] at h_len
    subst h_len
    have := HyperEnv.Perm_singleton_singleton.mp hP
    simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq,
      Prod.mk.injEq, and_true] at this
    exfalso ; exact hxl this.1.symm
  case bot =>
    expose_names
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_cons, List.length_nil, zero_add, List.length_append, Nat.right_eq_add,
      List.length_eq_zero_iff, Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.union_empty,
      Finset.mem_singleton] at h_len hxl
    subst h_len
    have hP' := HyperEnv.Perm_singleton_singleton.mp hP
    have hx_in_LHS : (x, A) ∈ (x_1 ∶ ⊥ :: Γ_1) := by
      exact (List.Perm.mem_iff hP'.symm).mp (by simp)
    simp only [List.mem_cons] at hx_in_LHS
    have hx_in_Γ_1 : (x, A) ∈ Γ_1 := by
      rcases hx_in_LHS with ⟨rfl, _⟩ | h
      · exfalso
        exact hxl rfl
      · exact h
    obtain ⟨Γ'_next, h_extract⟩ := Env.exists_perm_cons hx_in_Γ_1
    use [], Γ'_next
    rw [HyperEnv.merge_nilL]
    apply HyperEnv.Perm_singleton_singleton.mpr
    exact h_extract
  case tensor =>
    expose_names
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_cons, List.length_nil, zero_add, List.length_append, Nat.right_eq_add,
      List.length_eq_zero_iff, Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.singleton_union,
      Finset.mem_insert, Finset.mem_singleton, not_or] at h_len hxl
    subst h_len
    have hP' := HyperEnv.Perm_singleton_singleton.mp hP
    have hx_in_LHS : (x, A) ∈ x_1 ∶ A_1 ⨂ B :: Γ_1 ++ Δ := by
      exact (List.Perm.mem_iff hP'.symm).mp (by simp)
    simp only [List.mem_cons, List.mem_append] at hx_in_LHS
    have h_split : (x, A) ∈ Γ_1 ∨ (x, A) ∈ Δ := by
      rcases hx_in_LHS with h1 | h2
      · rcases h1 with ⟨rfl, _⟩ | h
        · exfalso ; exact hxl.1 (by rfl)
        · left ; exact h
      · right ; exact h2
    rcases h_split with h_in_Γ_1 | h_in_Δ
    · obtain ⟨Γ'_next, h_extract⟩ := Env.exists_perm_cons h_in_Γ_1
      use [x_1 ∶ B :: Δ], y ∶ A_1 :: Γ'_next
      have h_env_perm : y ∶ A_1 :: Γ_1 ~ x ∶ A :: y ∶ A_1 :: Γ'_next := by
        apply List.Perm.trans
        · apply List.Perm.cons
          exact h_extract
        · apply List.Perm.swap
      have h_hyper_perm := HyperEnv.Perm_singleton_singleton.mpr h_env_perm
      exact HyperEnv.Perm.merge_comm.trans (HyperEnv.Perm.merge_left h_hyper_perm _)
    · obtain ⟨Δ'_next, h_extract⟩ := Env.exists_perm_cons h_in_Δ
      use [y ∶ A_1 :: Γ_1], x_1 ∶ B :: Δ'_next
      have h_env_perm : x_1 ∶ B :: Δ ~ x ∶ A :: x_1 ∶ B :: Δ'_next := by
        apply List.Perm.trans
        · apply List.Perm.cons
          exact h_extract
        · apply List.Perm.swap
      have h_hyper_perm := HyperEnv.Perm_singleton_singleton.mpr h_env_perm
      exact HyperEnv.Perm.merge_left h_hyper_perm _
  case parr =>
    expose_names
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_cons, List.length_nil, zero_add, List.length_append, Nat.right_eq_add,
      List.length_eq_zero_iff, Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.singleton_union,
      Finset.mem_insert, Finset.mem_singleton, not_or] at h_len hxl
    subst h_len
    have hP' := HyperEnv.Perm_singleton_singleton.mp hP
    have hx_in_LHS : (x, A) ∈ (x_1 ∶ A_1 ⅋ B :: Γ_1) := by
      exact (List.Perm.mem_iff hP'.symm).mp (by simp)
    simp only [List.mem_cons] at hx_in_LHS
    have hx_in_Γ_1 : (x, A) ∈ Γ_1 := by
      rcases hx_in_LHS with ⟨rfl, _⟩ | h
      · exfalso
        exact hxl.1 rfl
      · exact h
    obtain ⟨Γ'_next, h_extract⟩ := Env.exists_perm_cons hx_in_Γ_1
    use [], y ∶ A_1 :: x_1 ∶ B :: Γ'_next
    rw [HyperEnv.merge_nilL]
    apply HyperEnv.Perm_singleton_singleton.mpr
    apply List.Perm.trans
    · apply List.Perm.cons
      apply List.Perm.cons
      exact h_extract
    · apply List.Perm.trans
      · apply List.Perm.cons
        apply List.Perm.swap
      · apply List.Perm.swap
  case par₁ =>
    expose_names
    have h_split := HyperEnv.Perm_merge_inv_one hP
    rcases h_split with ⟨𝒢ᵣ, hG, hJ⟩ | ⟨ℋᵣ, hH, hJ⟩
    · obtain ⟨𝒢'_next, Γ', h_post⟩ := h_ih hxl hG
      use 𝒢'_next |ₕ ℋ_1, Γ'
      have h_stapled := HyperEnv.Perm.merge_right h_post ℋ_1
      have h_swapped : 𝒢'_next |ₕ [x ∶ A :: Γ'] |ₕ ℋ_1 ~
        𝒢'_next |ₕ ℋ_1 |ₕ [x ∶ A :: Γ'] := by
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        exact HyperEnv.Perm.merge_comm
      exact h_stapled.trans h_swapped
    · use 𝒢'_1 |ₕ ℋᵣ, Γ
      have h_stapled := HyperEnv.Perm.merge_left hH 𝒢'_1
      rw [← HyperEnv.merge_assoc] at h_stapled
      exact h_stapled
  case par₂ =>
    expose_names
    have h_split := HyperEnv.Perm_merge_inv_one hP
    rcases h_split with ⟨𝒢ᵣ, hG, hJ⟩ | ⟨ℋᵣ, hH, hJ⟩
    · use 𝒢ᵣ |ₕ ℋ', Γ
      have h_stapled := HyperEnv.Perm.merge_right hG ℋ'
      have h_swapped : 𝒢ᵣ |ₕ [x ∶ A :: Γ] |ₕ ℋ' ~
        𝒢ᵣ |ₕ ℋ' |ₕ [x ∶ A :: Γ] := by
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        exact HyperEnv.Perm.merge_comm
      exact h_stapled.trans h_swapped
    · obtain ⟨ℋ'_next, Γ', h_post⟩ := h_ih hxl hH
      use 𝒢_1 |ₕ ℋ'_next, Γ'
      have h_stapled := HyperEnv.Perm.merge_left h_post 𝒢_1
      rw [← HyperEnv.merge_assoc] at h_stapled
      exact h_stapled
  case syn =>
    expose_names
    simp only [Lbl.f, Lbl.i, Finset.notMem_union, and_assoc] at hxl h₁_ih h₂_ih
    have h_split := HyperEnv.Perm_merge_inv_one hP
    rcases h_split with ⟨𝒢ᵣ, hG, hJ⟩ | ⟨ℋᵣ, hH, hJ⟩
    · obtain ⟨𝒢'_next, Γ', h_post⟩ := h₁_ih ⟨hxl.1, hxl.2.2.1⟩ hG
      use 𝒢'_next |ₕ ℋ', Γ'
      have h_stapled := HyperEnv.Perm.merge_right h_post ℋ'
      have h_swapped : 𝒢'_next |ₕ [x ∶ A :: Γ'] |ₕ ℋ' ~
        𝒢'_next |ₕ ℋ' |ₕ [x ∶ A :: Γ'] := by
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        exact HyperEnv.Perm.merge_comm
      exact h_stapled.trans h_swapped
    · obtain ⟨ℋ'_next, Γ', h_post⟩ := h₂_ih  ⟨hxl.2.1, hxl.2.2.2⟩ hH
      use 𝒢'_1 |ₕ ℋ'_next, Γ'
      have h_stapled := HyperEnv.Perm.merge_left h_post 𝒢'_1
      rw [← HyperEnv.merge_assoc] at h_stapled
      exact h_stapled
  case one_bot =>
    use 𝒢', Γ
  case tensor_parr =>
    use 𝒢', Γ
    rw [← Env.merge_assoc]
    exact hP
  case res ih =>
    expose_names
    have h_split := HyperEnv.Perm_merge_inv_one hP
    rcases h_split with ⟨𝒢ᵣ, hG, hJ⟩ | ⟨ℋᵣ, hH, hJ⟩
    · have h_pre_inner : 𝒢_1 |ₕ [x_1 ∶ A_1 :: Γ_1] |ₕ [y ∶ A_1ᗮ :: Δ] ~
          (𝒢ᵣ |ₕ [x_1 ∶ A_1 :: Γ_1] |ₕ [y ∶ A_1ᗮ :: Δ]) |ₕ [x ∶ A :: Γ] := by
        apply HyperEnv.Perm_rotate_rhs_right
        repeat rw [← HyperEnv.merge_assoc]
        rw [HyperEnv.merge_assoc]
        conv_rhs => rw [HyperEnv.merge_assoc]
        exact HyperEnv.Perm.merge (hG.trans HyperEnv.Perm.merge_comm) (by rfl)
      obtain ⟨𝒢'_post, Γ'_post, h_post⟩ := ih hxl h_pre_inner
      rw [HyperEnv.merge_assoc] at h_post
      have h_split_post := HyperEnv.Perm_merge_inv_one h_post
      rcases h_split_post with ⟨𝒢'_1ᵣ, hG_post, hJ_post⟩ | ⟨ℋ_post, hH_post, hJ_post⟩
      · use 𝒢'_1ᵣ |ₕ [Γ'‚ Δ'], Γ'_post
        have h_stapled := HyperEnv.Perm.merge_right hG_post [Γ'‚ Δ']
        have h_swapped : 𝒢'_1ᵣ |ₕ [x ∶ A :: Γ'_post] |ₕ [Γ'‚ Δ'] ~
          𝒢'_1ᵣ |ₕ [Γ'‚ Δ'] |ₕ [x ∶ A :: Γ'_post] := by
          apply HyperEnv.Perm_rotate_rhs_right
          apply HyperEnv.Perm_merge_cancel_right_inv
          exact HyperEnv.Perm.merge_comm
        exact h_stapled.trans h_swapped
      · exfalso
        have hx_in_G1 : x ∈ 𝒢_1.names := by
          have h_mem : x ∶ A :: Γ ∈ 𝒢ᵣ |ₕ [x ∶ A :: Γ] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem hG h_mem
          have h' := (List.Perm.mem_iff (a := x ∶ A) hPE).mpr (by simp)
          exact HyperEnv.mem_of_mem_mem_names h' hE

        have h_mem_RHS : x ∶ A :: Γ'_post ∈ ℋ_post |ₕ [x ∶ A :: Γ'_post] := by simp
        obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem hH_post h_mem_RHS
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hE

        rcases hE with rfl | rfl
        · have h_mem := (List.Perm.mem_iff (a := x ∶ A) hPE.symm).mp (by simp)
          simp only [List.mem_cons, Prod.mk.injEq] at h_mem
          rcases h_mem with ⟨rfl, _⟩ | _
          · have h_contra : x ∈ P_1.f ∪ 𝒢_1.names ∪ Γ_1.names ∪ Δ.names := by
              simp only [Finset.union_assoc, Finset.mem_union]; right; left; exact hx_in_G1
            exact hx_pre h_contra
          · sorry

        · have h_mem := (List.Perm.mem_iff (a := x ∶ A) hPE.symm).mp (by simp)
          simp only [List.mem_cons, Prod.mk.injEq] at h_mem
          rcases h_mem with ⟨rfl, _⟩ | _
          · have h_contra : x ∈ P_1.f ∪ 𝒢_1.names ∪ Γ_1.names ∪ Δ.names := by
              simp only [Finset.union_assoc, Finset.mem_union]; right; left; exact hx_in_G1
            exact hy_pre h_contra
          · sorry
    · have h_comb_perm : Γ_1‚ Δ ~ x ∶ A :: Γ := by
        obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem (Γ := x ∶ A :: Γ) hH (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
        subst hE
        exact hPE
      have h_x1_in : x_1 ∶ A_1 :: Γ_1 ∈ 𝒢_1 |ₕ [x_1 ∶ A_1 :: Γ_1] |ₕ [y ∶ A_1ᗮ :: Δ] := by simp
      have h_x1_disj : Disjoint (Env.names (x_1 ∶ A_1 :: Γ_1)) (l_1.f ∪ l_1.i) := by
        sorry

      obtain ⟨x1_post, h_x1_post_in, h_x1_post_perm⟩ :=
        TypingStepₘ_preserves_block hStep h_x1_in h_x1_disj

      have h_Γ_perm : Γ' ~ Γ_1 := by
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at h_x1_post_in
        rcases h_x1_post_in with h_in_G'1 | rfl | rfl
        · have h' := (List.Perm.mem_iff (a := x_1 ∶ A_1) h_x1_post_perm).mpr (by simp)
          have h'' := HyperEnv.mem_of_mem_mem_names h' h_in_G'1
          exact False.elim (hx_post (by simp [h'']))
        · exact List.Perm.cons_inv h_x1_post_perm
        · have h' := (List.Perm.mem_iff (a := x_1 ∶ A_1) h_x1_post_perm).mpr (by simp)
          simp only [List.mem_cons, Prod.mk.injEq] at h'
          rcases h' with ⟨rfl, _⟩ | hΔ'
          · exact False.elim (hneq (by rfl))
          · have : x_1 ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
              simp only [Finset.union_assoc, Finset.mem_union] ; right ; right ; right
              exact Env.mem_pair_fst_in_names _ hΔ'
            exact False.elim (hx_post this)

      have h_y_in : y ∶ A_1ᗮ :: Δ ∈ 𝒢_1 |ₕ [x_1 ∶ A_1 :: Γ_1] |ₕ [y ∶ A_1ᗮ :: Δ] := by simp
      have h_y_disj : Disjoint (Env.names (y ∶ A_1ᗮ :: Δ)) (l_1.f ∪ l_1.i) := by
        sorry

      obtain ⟨y_post, h_y_post_in, h_y_post_perm⟩ :=
        TypingStepₘ_preserves_block hStep h_y_in h_y_disj

      have h_Δ_perm : Δ' ~ Δ := by
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at h_y_post_in
        rcases h_y_post_in with h_in_G'1 | rfl | rfl
        · have h' := (List.Perm.mem_iff (a := y ∶ A_1ᗮ) h_y_post_perm).mpr (by simp)
          have h'' := HyperEnv.mem_of_mem_mem_names h' h_in_G'1
          exact False.elim (hy_post (by simp [h'']))
        · have h' := (List.Perm.mem_iff (a := y ∶ A_1ᗮ) h_y_post_perm).mpr (by simp)
          simp only [List.mem_cons, Prod.mk.injEq] at h'
          rcases h' with ⟨rfl, _⟩ | hΓ'
          · exact False.elim (hneq.symm (by rfl))
          · have : y ∈ P'_1.f ∪ 𝒢'_1.names ∪ Γ'.names ∪ Δ'.names := by
              simp only [Finset.union_assoc, Finset.mem_union] ; right ; right ; left
              exact Env.mem_pair_fst_in_names _ hΓ'
            exact False.elim (hy_post this)
        · exact List.Perm.cons_inv h_y_post_perm
      have h_comb_post_perm : Γ'‚ Δ' ~ Γ_1‚ Δ := List.Perm.append h_Γ_perm h_Δ_perm
      have h_final_block : Γ'‚ Δ' ~ x ∶ A :: Γ := h_comb_post_perm.trans h_comb_perm
      use 𝒢'_1, Γ
      exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_final_block)

  case perm_env =>
    expose_names
    have : Γ_1 :: 𝒢_1 ~ Γ' :: 𝒢_1 := HyperEnv.Perm.cons hP1 (by rfl)
    obtain ⟨𝒢'_next, Γ', h_post⟩ := hTS_ih hxl (this.trans hP)
    use 𝒢'_next, Γ'
  case perm_hyper =>
    expose_names
    obtain ⟨𝒢'_next, Γ', h_post⟩ := hTS_ih hxl (hP1.trans hP)
    use 𝒢'_next, Γ'
    exact hP2.symm.trans h_post

lemma TypingStepₘ_preserves_disjoint_or_merges {n n' : Nat} {P P' : Proc}
  {𝒢_pre ℋ : HyperEnv} {l : Lbl} {𝒟' : n' ⊢ P' ∷ ℋ}
  {𝒢 : HyperEnv} {Γ Δ : Env} {A : Types} {x y : FPName}
  (𝒟 : n ⊢ P ∷ 𝒢_pre) (hStep : TypingStepₘ 𝒟 l 𝒟')
  (hxl : x ∉ l.f ∪ l.i) (hyl : y ∉ l.f ∪ l.i)
  (hP : 𝒢_pre ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) :
  (∃ 𝒢' Γ' Δ', ℋ ~ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) ∨
  (∃ 𝒢' Ξ', ℋ ~ 𝒢' |ₕ [x ∶ A :: Ξ' ++ [y ∶ Aᗮ]]) := by
  induction hStep generalizing 𝒢 Γ Δ

  case one | bot | tensor | parr =>
    exfalso
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_cons, List.length_nil, zero_add, List.append_assoc, List.cons_append,
      List.nil_append, List.length_append, Nat.reduceAdd, Nat.right_eq_add, Nat.add_eq_zero_iff,
      List.length_eq_zero_iff, one_ne_zero, and_false] at h_len

  case par₁ =>
    expose_names
    have h_split := HyperEnv.Perm_merge_inv_two_blocks hP
    rcases h_split with ⟨𝒢ᵣ, hG, hJ⟩ | ⟨ℋᵣ, hH, hJ⟩ |
      ⟨𝒢ᵣ, ℋᵣ, hG, hH, hJ⟩ | ⟨𝒢ᵣ, ℋᵣ, hG, hH, hJ⟩
    · obtain h_disj | h_cross := h_ih hxl hyl hG
      · rcases h_disj with ⟨𝒢'_next, Γ', Δ', h_post⟩
        left
        use 𝒢'_next |ₕ ℋ_1, Γ', Δ'
        have h_stapled := HyperEnv.Perm.merge_right h_post ℋ_1
        have h_grouped : 𝒢'_next |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] |ₕ ℋ_1 ~
          𝒢'_next |ₕ ℋ_1 |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
          apply HyperEnv.Perm_rotate_rhs_left
          rw [← HyperEnv.merge_assoc]
          apply HyperEnv.Perm_merge_cancel_right_inv
          apply HyperEnv.Perm_rotate_rhs_right
          rfl
        exact h_stapled.trans h_grouped
      · rcases h_cross with ⟨𝒢'_next, Ξ', h_post⟩
        right
        use 𝒢'_next |ₕ ℋ_1, Ξ'
        have h_stapled := HyperEnv.Perm.merge_right h_post ℋ_1
        have h_swapped := HyperEnv.Perm_pull_rhs_mid_right h_stapled
        exact h_swapped
    · left
      use 𝒢' |ₕ ℋᵣ, Γ, Δ
      have h_stapled := HyperEnv.Perm.merge_left hH 𝒢'
      repeat rw [← HyperEnv.merge_assoc] at h_stapled
      exact h_stapled
    ·

      sorry
    · sorry




  case par₂ => sorry




  case syn => sorry
  case one_bot => sorry
  case tensor_parr => sorry
  case res => sorry

  case perm_env =>
    expose_names
    have h_head_perm : Γ_1 :: 𝒢_1 ~ Γ' :: 𝒢_1 :=
      HyperEnv.Perm.cons hP1 HyperEnv.Perm.rfl
    have h_inner_perm : Γ_1 :: 𝒢_1 ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] :=
      h_head_perm.trans hP
    exact hTS_ih hxl hyl h_inner_perm
  case perm_hyper =>
    expose_names
    have h_inner_perm : 𝒢_1 ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] := hP1.trans hP
    obtain h_disj | h_cross := hTS_ih hxl hyl h_inner_perm
    · rcases h_disj with ⟨𝒢_next, Γ', Δ', h_post⟩
      left ; exact ⟨𝒢_next, Γ', Δ', hP2.symm.trans h_post⟩
    · rcases h_cross with ⟨𝒢_next, Ξ', h_post⟩
      right ; exact ⟨𝒢_next, Ξ', hP2.symm.trans h_post⟩





















-- TODO: Move ProcStep, EnvStep, and Typing and HyperEnv lemmas to respective files
-- TODO: Prove Session fidelity, erasure, type preservation, Session fidelity for πLL
-- TODO: Delete Single files in favor of the new folder structure


-- FIXME: Typing_preserves_proc_congr
-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs

-- FIXME: Prove name substitution only being applied to free names?
--        (Basically just Typing_f_eq_names since 𝒢.names = P.f => Typing.substNames is
--         being applied to P.f)


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }
-- NOTE: Remember that lemmas exist for duplicating a process and disposing

-- TODO: Find different syntax for open?
-- TODO: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere
/- TODO:
  Refine / organize the various "Lemmas" folders to be more organized instead of
  simply throwing every lemma into one file
-/
-- TODO: Change lemma naminig and dot notation interactions to follow standard pattern
-- TODO: Change HyperEnv.Nodup def to match Env
-- TODO: Edit files to follow the new linters lean has added
/- TODO:
  - Maybe remove all_fresh from one_bot signature and make it like tensor_parr and
  do inline induction instead.
-/
