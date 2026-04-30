import PiLL.Model.HyperEnvironment.Lemmas.Basic

lemma HyperEnv.Perm.extract_one_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[z ∶ 1]])
  (h_post : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ)
  (hzx : z ≠ x) (hzy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ',
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ' |ₕ [[z ∶ 1]] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ' := by
  have hzin : ([z ∶ 1]) ∈ 𝒢ᵣ |ₕ [[z ∶ 1]] := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hzin
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ : ∃ 𝒢ᵣ, 𝒢 ~ E :: 𝒢ᵣ :=
        HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' : 𝒢 ~ [z ∶ 1] :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], ?_, ?_⟩
      · have := h𝒢_split.symm.trans h𝒢'
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm.merge
        · rw [HyperEnv.cons_append] at h𝒢'
          exact h𝒢'
        · rfl
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] := by
          have h_pre_subst : ([z ∶ 1] :: 𝒢ᵣ') |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~
            𝒢ᵣ |ₕ [[z ∶ 1]] := by
            simp only [HasPerm.perm, List.perm_singleton] at hPE
            subst hPE
            apply HyperEnv.Perm.merge_right (𝒥 := [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) at h𝒢_split
            simp only [← HyperEnv.merge_assoc] at h𝒢_split
            exact h𝒢_split.symm.trans h_pre
          rw [HyperEnv.cons_append, HyperEnv.merge_assoc] at h_pre_subst
          symm at h_pre_subst
          apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          rw [HyperEnv.merge_assoc]
          exact h_pre_subst
        have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
          𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] :=
          h_post.trans h𝒢ᵣ
        have hPΓΓ' : x ∶ A :: Γ' ~ x ∶ A :: Γ := by
          have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEx : (x, A) ∈ E := by
                have := hPE.symm.subset
                simp only [List.cons_subset] at this
                obtain ⟨h1, h2⟩ := this
                exact h1
              have hx𝒢: x ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEx))
              apply hFx hx𝒢
            case inr h =>
              subst h
              apply List.Perm.symm
              exact hPE
          · exfalso
            have hxiny : (x, A) ∈ y ∶ Aᗮ :: Δ := by
              have := hPE.symm.subset
              simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
              exact this.1
            simp only [List.mem_cons, Prod.mk.injEq] at hxiny
            rcases hxiny with heq | hΔ
            · rw [heq.1] at hneq
              contradiction
            · exact hxΔ (Env.mem_pair_fst_in_names _ hΔ)
        have hPΔΔ' : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δ := by
          have hxin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEy : (y, Aᗮ) ∈ E := by
                have := hPE.symm.subset
                simp only [List.cons_subset] at this
                obtain ⟨h1, h2⟩ := this
                exact h1
              have hy𝒢: y ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEy))
              apply hFy hy𝒢
            case inr h =>
              exfalso
              subst h
              have hyinx : (y, Aᗮ) ∈ x ∶ A :: Γ := by
                have := hPE.symm.subset
                simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
                exact this.1
              simp only [List.mem_cons, Prod.mk.injEq] at hyinx
              cases hyinx
              case inl h =>
                rw [h.1] at hneq
                contradiction
              case inr h =>
                exact hyΓ (Env.mem_pair_fst_in_names _ h)
          · simp only [HasPerm.perm, List.perm_cons] at hPE ⊢
            exact hPE.symm
        have hPℋ𝒢 : ℋ ~ 𝒢ᵣ' := by
          have hP1 : 𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~
            𝒢ᵣ' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm.merge
              · rfl
              · exact HyperEnv.Perm.cons hPΓΓ'.symm rfl
            · exact HyperEnv.Perm.cons hPΔΔ'.symm rfl
          apply HyperEnv.Perm_merge_cancel_right (𝒥 := [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'])
          simp only [← HyperEnv.merge_assoc]
          exact h_post_subst.trans hP1
        apply HyperEnv.Perm.merge
        · exact hPℋ𝒢
        · apply HyperEnv.Perm.cons
          · apply List.Perm.append
            · exact List.Perm.cons_inv (a := x ∶ A) hPΓΓ'
            · exact List.Perm.cons_inv (a := y ∶ Aᗮ) hPΔΔ'
          · rfl
    case inr h =>
      rw [h] at hPE
      simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
      rw [hPE.1.1] at hzx
      contradiction
  · exfalso
    simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
    rw [hPE.1.1] at hzy
    contradiction
