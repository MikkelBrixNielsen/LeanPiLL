import PiLL.Model.HyperEnvironment.Lemmas.Basic

set_option maxHeartbeats 250000 in
-- 200000 heartbeats isn't enough for it to typecheck
lemma HyperEnv.Perm.extract_tensor_parr_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Γ'' Δ Δ' Δ'' Ξ : Env}
  {u v x x' y y' : FPName} {A B C D E : Types}
  (h_pre : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
    𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ])
  (h_post : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
     𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ])
  (hux : u ≠ x) (hux' : u ≠ x') (huy : u ≠ y) (huy' : u ≠ y')
  (hvx : v ≠ x) (hvx' : v ≠ x') (hvy : v ≠ y) (hvy' : v ≠ y')
  (huv : u ≠ v) (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (huΔ' : u ∉ Δ'.names) (hvΓ' : v ∉ Γ'.names) :
  (∃ 𝒢ₙ Γₙ Δₙ Ξₙ, -- components kept separate
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ] |ₕ [y ∶ C ⅋ D :: Ξₙ] ∧
    ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [x ∶ B :: Δₙ] |ₕ [x' ∶ A :: Γₙ] |ₕ [y' ∶ C :: y ∶ D :: Ξₙ])
  ∨
  (∃ 𝒢ₙ Γₙ Δₙ Ξₙ,
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ ++ y ∶ C ⅋ D :: Ξₙ] ∧
      (ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [x ∶ B :: Δₙ] |ₕ [x' ∶ A :: Γₙ ++ y' ∶ C :: y ∶ D :: Ξₙ] ∨
       ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [x' ∶ A :: Γₙ] |ₕ [x ∶ B :: Δₙ ++ y' ∶ C :: y ∶ D :: Ξₙ])) := by
  have huin : u ∶ E :: Γ' ∈ 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by simp
  have hvin : v ∶ Eᗮ :: Δ' ∈ 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by simp
  obtain ⟨Eu, hEu, hPEu⟩ := HyperEnv.Perm_mem h_pre.symm huin
  obtain ⟨Ev, hEv, hPEv⟩ := HyperEnv.Perm_mem h_pre.symm hvin
  simp only [List.mem_append, List.mem_singleton, or_assoc] at hEu hEv
  rcases hEu with hu𝒢 | rfl | rfl
  · rcases hEv with hv𝒢 | rfl | rfl
    · left -- Both in 𝒢ᵣ => didn't merge use LHS of OR
      obtain ⟨𝒢ᵣ', hP𝒢ᵣ'⟩ := HyperEnv.exists_perm_cons_of_mem hu𝒢
      obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP𝒢ᵣ'.symm hv𝒢
      simp only [List.mem_cons] at hE1
      rcases hE1 with rfl | hE𝒢
      · exfalso
        have hPEuv := hPEu.symm.trans (hPE1.trans hPEv)
        have huinv := (List.Perm.mem_iff (a := (u, E)) hPEuv).mp (by simp)
        simp at huinv
        rcases huinv with ⟨rfl, _⟩ | h
        · exact huv (by rfl)
        · exact huΔ' (Env.mem_pair_fst_in_names _ h)
      · obtain ⟨𝒢ₙ, hP𝒢ₙ⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
        refine ⟨𝒢ₙ |ₕ [Γ'‚ Δ'], Γ, Δ, Ξ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := hP𝒢ᵣ'.trans (HyperEnv.Perm.cons (List.Perm.refl _) hP𝒢ₙ)
            have hP2 : Eu :: E1 :: 𝒢ₙ ~ (u ∶ E :: Γ') :: (v ∶ Eᗮ :: Δ') :: 𝒢ₙ :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.cons (hPE1.trans hPEv) (HyperEnv.Perm.refl _))
            have hP3 : (u ∶ E :: Γ') :: (v ∶ Eᗮ :: Δ') :: 𝒢ₙ ~
              𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.cons_append, HyperEnv.cons_append (Γ := v ∶ Eᗮ :: Δ') (𝒢 := 𝒢ₙ),
                  ← HyperEnv.merge_assoc]
            exact hP1.trans (hP2.trans hP3)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : 𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] |ₕ
                [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              repeat rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm.merge ?_ (by rfl)
              apply HyperEnv.Perm.merge ?_ (by rfl)
              exact HyperEnv.Perm_rotate_rhs_right (by rfl)
            exact hP1.trans hP2
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP3 := HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])
          have hP4 : (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [Γ'‚ Δ'] ~
            (𝒢ₙ |ₕ [Γ'‚ Δ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            conv_rhs => rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            apply HyperEnv.Perm_rotate_rhs_right
            rfl
          exact hP3.trans hP4
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hPE1v : E1 ~ v ∶ Eᗮ :: Δ' := hPE1.trans hPEv
            have hP1 := hP𝒢ᵣ'.trans (HyperEnv.Perm.cons (List.Perm.refl _) hP𝒢ₙ)
            have hP2 : Eu :: E1 :: 𝒢ₙ ~ (u ∶ E :: Γ') :: (v ∶ Eᗮ :: Δ') :: 𝒢ₙ :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.cons hPE1v (HyperEnv.Perm.refl _))
            have hP3 : (u ∶ E :: Γ') :: (v ∶ Eᗮ :: Δ') :: 𝒢ₙ ~
              𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.cons_append, HyperEnv.cons_append (Γ := v ∶ Eᗮ :: Δ') (𝒢 := 𝒢ₙ),
                  ← HyperEnv.merge_assoc]
            exact hP1.trans (hP2.trans hP3)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ₙ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_post.trans ((((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : 𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] |ₕ
              [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              𝒢ₙ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              conv_rhs => rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_right
              simp only [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              rfl
            exact hP1.trans hP2
          have h𝒢 : 𝒢 ~ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : 𝒢ₙ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] |ₕ
              [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              repeat rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm.merge ?_ (by rfl)
              apply HyperEnv.Perm.merge ?_ (by rfl)
              exact HyperEnv.Perm_rotate_rhs_right (by rfl)
            have hP3 := hP1.trans hP2
            apply HyperEnv.Perm_merge_cancel_right at hP3
            apply HyperEnv.Perm_merge_cancel_right at hP3
            exact hP3
          have hPΓ'' : Γ'' ~ Γ' := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ₙ | rfl | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ₙ]
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux (by rfl)
              · have hCell : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux' (by rfl)
              · have hCell : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hCell : (u, E) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact huΔ' (Env.mem_pair_fst_in_names _ h)
          have hPΔ'' : Δ'' ~ Δ' := by
            have hin_v : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hin_v
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ₙ | rfl | rfl | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ₙ]
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hv𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx (by rfl)
              · have hCell : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx' (by rfl)
              · have hCell : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hCell : (v, Eᗮ) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvΓ' (Env.mem_pair_fst_in_names _ h)
            · exact List.Perm.cons_inv hPE'.symm
          have h_post_matched : ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ₙ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have h1 : [u ∶ E :: Γ''] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have h2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~ ℋ |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) h1) h2
            exact hLHS.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at h_post_matched
          apply HyperEnv.Perm_merge_cancel_right at h_post_matched
          have hP1 := HyperEnv.Perm.merge h_post_matched (HyperEnv.Perm.refl [Γ''‚ Δ''])
          have hP2 : (𝒢ₙ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [Γ''‚ Δ''] ~
            (𝒢ₙ |ₕ [Γ'‚ Δ']) |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
            conv_rhs => rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm_rotate_rhs_right
              rw [← HyperEnv.merge_assoc]
            · rw [HyperEnv.Perm_singleton_singleton]
              exact List.Perm.append hPΓ'' hPΔ''
          exact hP1.trans hP2
    · left -- x merged with a background block, y safe
      obtain ⟨𝒢ᵣ', hP𝒢ᵣ'⟩ := HyperEnv.exists_perm_cons_of_mem hu𝒢
      have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPEv.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_append] at hvin
      have h𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by
          have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]
              apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 := HyperEnv.Perm_singleton_singleton.mpr hPEv
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              conv_rhs => rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              rfl
            apply hP1.trans (((HyperEnv.Perm.merge (by rfl) (hP2)).merge (by rfl)).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          exact h_pre_subst
      rcases hvin with ⟨rfl, _⟩ | hvΓ | hvΔ
      · exfalso ; exact hvx (by rfl)
      · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (v, Eᗮ) :: Γᵣ := Env.exists_perm_cons hvΓ
        have hPΔ' : Δ' ~ x ∶ A ⨂ B :: Γᵣ ++ Δ := by
          have hP1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append hPΓ (List.Perm.refl Δ)))
          exact ((hPEv.symm.trans hP1).trans (List.Perm.swap ..)).cons_inv
        refine ⟨𝒢ᵣ', (Γ'‚ Γᵣ), Δ, Ξ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]
              apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
              have hP31 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              (HyperEnv.Perm.merge (by rfl) hP31).merge (by rfl)
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP31 : 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                rfl
              have hP32 : 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact hP31.trans hP32
            exact hP1.trans (hP2.trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP1 : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hP11 := List.Perm.append (List.Perm.refl Γ') hPΔ'
            have hP12 : Γ' ++ (x ∶ A ⨂ B :: Γᵣ ++ Δ) ~ x ∶ A ⨂ B :: (Γ' ++ Γᵣ ++ Δ) := by
              rw [List.append_assoc]
              apply List.perm_middle
            exact hP11.trans hP12
          have hP2 := HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])
          have hP3 : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [Γ'‚ Δ'] ~
            𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have hP31 : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ] ~
              𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans hP31
          exact hP2.trans hP3
        · have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]
              apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
            have hP1 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : [x' ∶ A :: Γ] ~ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x' ∶ A) hPΓ).trans (List.Perm.swap ..)
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [x ∶ B :: Δ] |ₕ
                [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
              conv_rhs => rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
          have hPΓ'' : Γ'' ~ Γ' := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hCell : (u, E) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact hux' (by rfl)
              · have hΔ' := (List.Perm.mem_iff (a := (u, E)) hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
          have hPΔ'' : Δ'' ~ x' ∶ A :: Γᵣ := by
            have hinv' : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hvx (by rfl)
              · -- v ∈ Γ : v block in LHS maps to two blocks in RHS, cancelling one
                -- implies the other must hide inside ℋ or u block contradicting hFv' / huΔ'
                have hP1 := HyperEnv.Perm_singleton_singleton.mpr hPE'
                have hP2 := (HyperEnv.Perm.merge (by rfl) hP1).trans h_post_subst
                have hP3 : 𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                    [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] ~
                  (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: Γ'] |ₕ
                    [v ∶ Eᗮ :: x' ∶ A :: Γᵣ]) |ₕ [x ∶ B :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  conv_rhs => rw [← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                have hP4 := hP2.trans hP3
                apply HyperEnv.Perm_merge_cancel_right at hP4
                have hin : (v ∶ Eᗮ :: x' ∶ A :: Γᵣ) ∈ 𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                  [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by simp
                obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP4 hin
                simp only [List.mem_append, List.mem_singleton] at hE1
                rcases hE1 with hℋ | rfl
                · have hvE1 : (v, Eᗮ) ∈ E1 := (List.Perm.mem_iff hPE1.symm).mp (by simp)
                  exact hFv' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ hvE1))
                · have hin : (u, E) ∈ v ∶ Eᗮ :: x' ∶ A :: Γᵣ :=
                    (List.Perm.mem_iff hPE1).mp (by simp)
                  simp at hin
                  rcases hin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | huΓᵣ
                  · exact huv (by rfl)
                  · exact hux' (by rfl)
                  · have hu_Δ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [huΓᵣ])
                    exact huΔ' (Env.mem_pair_fst_in_names _ hu_Δ')
            · exfalso
              have huin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hCell : (v, Eᗮ) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvΓ' (Env.mem_pair_fst_in_names _ h)
            · exact List.Perm.cons_inv hPE'.symm
          have hP1 : ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
            have h1 : [u ∶ E :: Γ''] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have h2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) h1) h2
            exact hLHS.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP1
          apply HyperEnv.Perm_merge_cancel_right at hP1
          have hP2 : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ'‚ Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
            have hP21 : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [x' ∶ A :: Γ'‚ Γᵣ] ~
              𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ'‚ Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_left
              rfl
            have hP22 := (List.Perm.append hPΓ'' hPΔ'').trans (List.perm_middle)
            have hP23 := HyperEnv.Perm_singleton_singleton.mpr (hP22)
            exact (HyperEnv.Perm.merge (by rfl) (hP23)).trans hP21
          exact (HyperEnv.Perm.merge hP1 (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP2
      · obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (v, Eᗮ) :: Δᵣ := Env.exists_perm_cons hvΔ
        have hPΔ' : Δ' ~ x ∶ A ⨂ B :: Γ ++ Δᵣ := by
          have h1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append (List.Perm.refl Γ) hPΔ))
          have h2 : Γ‚ ((v, Eᗮ) :: Δᵣ) ~ (v, Eᗮ) :: Γ ++ Δᵣ := List.perm_middle
          have h3 := List.Perm.cons (x ∶ A ⨂ B) h2
          exact ((hPEv.symm.trans h1).trans (h3.trans (List.Perm.swap ..))).cons_inv
        refine ⟨𝒢ᵣ', Γ, (Γ'‚ Δᵣ), Ξ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]
              apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEv
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP31 : 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                rfl
              have hP32 : 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact hP31.trans hP32
            exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP1 : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γ‚ (Γ' ++ Δᵣ)] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hP11 := List.Perm.append (List.Perm.refl Γ') hPΔ'
            have hP12 : Γ'‚ ((x ∶ A ⨂ B :: Γ)‚ Δᵣ) ~ x ∶ A ⨂ B :: Γ‚ Γ'‚ Δᵣ := by
              have hP121 : Γ'‚ (x ∶ A ⨂ B :: Γ‚ Δᵣ) ~ x ∶ A ⨂ B :: Γ'‚ Γ‚ Δᵣ := by
                rw [Env.merge_assoc]
                apply List.perm_middle
              have hP122 : Γ'‚ Γ‚ Δᵣ ~ Γ‚ Γ'‚ Δᵣ := List.Perm.append List.perm_append_comm (by rfl)
              exact hP121.trans (List.Perm.cons _ hP122)
            rw [Env.merge_assoc] at hP12
            exact hP11.trans hP12
          have hP2 : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [Γ'‚ Δ'] ~
            𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ (Γ' ++ Δᵣ)] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have this : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [x ∶ A ⨂ B :: Γ‚ (Γ' ++ Δᵣ)] ~
              𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ (Γ' ++ Δᵣ)] |ₕ [y ∶ C ⅋ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans this
          exact (HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans hP2
        · have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
             HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]
              apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
            have hP1 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : [x ∶ B :: Δ] ~ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x ∶ B) hPΔ).trans (List.Perm.swap ..)
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] |ₕ
                [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
              conv_rhs => rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_right
              simp only [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              rfl
            exact hP1.trans
              ((((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).merge (by rfl)).trans hP3)
          have hPΓ'' : Γ'' ~ Γ' := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux' (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hCell : (u, E) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact hux (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
          have hPΔ'' : Δ'' ~ x ∶ B :: Δᵣ := by
            have hinv'  : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hv𝒢_mem : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢_mem))
            · exfalso
              -- v ∈ Δ : mirror of v ∈ Γ case from earlier
              have hP1 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [x' ∶ A :: Γ] ~
                ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                HyperEnv.Perm.merge (by rfl)
                  (HyperEnv.Perm_singleton_singleton.mpr hPE'.symm).symm
              have hP2 : 𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                  [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] ~
                (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: Γ'] |ₕ
                  [v ∶ Eᗮ :: x ∶ B :: Δᵣ]) |ₕ [x' ∶ A :: Γ] := by
                conv_lhs => rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_right
                simp only [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP3 := (hP1.trans h_post_subst).trans hP2
              apply HyperEnv.Perm_merge_cancel_right at hP3
              have hin : (v ∶ Eᗮ :: x ∶ B :: Δᵣ) ∈ 𝒢ᵣ' |ₕ
                [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem hP3 hin
              simp only [List.mem_append, List.mem_singleton] at hE'
              rcases hE' with hℋ | rfl
              · have hvE : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                exact hFv' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ hvE))
              · have hin : (v, Eᗮ) ∈ u ∶ E :: Γ'' := (List.Perm.mem_iff hPE').mpr (by simp)
                simp at hin
                rcases hin with ⟨rfl, _⟩ | hvΓ''
                · exact huv.symm (by rfl)
                · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ'').mp hvΓ''
                  exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exfalso
              have hin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hin
              rcases hin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞ
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hCell : (v, Eᗮ) ∈ y ∶ C ⅋ D :: Ξ := by simp [hΞ]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvΓ' (Env.mem_pair_fst_in_names _ h)
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
            have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hP3 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP1) hP2
            exact hP3.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have : (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Γ' ++ Δᵣ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
            have hP21 : [Γ''‚ Δ''] ~ [x ∶ B :: Γ' ++ Δᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.append hPΓ'' hPΔ'').trans (List.perm_middle)
            have hP22 : (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [x ∶ B :: Γ' ++ Δᵣ] ~
              𝒢ᵣ' |ₕ [x ∶ B :: Γ' ++ Δᵣ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
              conv_rhs => rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              rfl
            exact (HyperEnv.Perm.merge (by rfl) hP21).trans hP22
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans this
    · left -- y merged with a background block, x safe
      obtain ⟨𝒢ᵣ', hP𝒢ᵣ'⟩ := HyperEnv.exists_perm_cons_of_mem hu𝒢
      have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPEv.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq] at hvin
      rcases hvin with ⟨rfl, _⟩ | hvΞ
      · exfalso ; exact hvy (by rfl)
      · obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (v, Eᗮ) :: Ξᵣ := Env.exists_perm_cons hvΞ
        have hPΔ' : Δ' ~ y ∶ C ⅋ D :: Ξᵣ := by
          have := hPEv.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
          exact (this.trans (List.Perm.swap ..)).cons_inv
        refine ⟨𝒢ᵣ', Γ, Δ, Γ' ++ Ξᵣ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEv
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [v ∶ Eᗮ :: Δ'] ~
              (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans ((HyperEnv.Perm.merge (by rfl) hP2).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP1 : [Γ'‚ Δ'] ~ [y ∶ C ⅋ D :: Γ' ++ Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hP11 := List.Perm.append (List.Perm.refl Γ') hPΔ'
            have hP12 : Γ' ++ y ∶ C ⅋ D :: Ξᵣ ~ y ∶ C ⅋ D :: Γ' ++ Ξᵣ := List.perm_middle
            exact hP11.trans hP12
          have hP2 := HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])
          exact hP2.trans (HyperEnv.Perm.merge (by rfl) hP1)
        · have h𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by
            have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
                HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
              have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
                rw [HyperEnv.cons_append] ; apply HyperEnv.Perm.merge_comm
              exact hP𝒢ᵣ'.trans (hP1.trans hP2)
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
              have hP2 : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2)).trans hP3)
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
            have hP1 : Eu :: 𝒢ᵣ' ~ (u ∶ E :: Γ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEu (HyperEnv.Perm.refl _)
            have hP2 : (u ∶ E :: Γ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [u ∶ E :: Γ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : [y' ∶ C :: y ∶ D :: Ξ] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP1 := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
              have hP2 : y' ∶ C :: y ∶ D :: (v, Eᗮ) :: Ξᵣ ~ (v, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ := by
                have : y' ∶ C :: y ∶ D :: (v, Eᗮ) :: Ξᵣ ~ y' ∶ C :: (v, Eᗮ) :: y ∶ D :: Ξᵣ :=
                  List.Perm.cons _ (List.Perm.swap ..)
                exact this.trans (List.Perm.swap ..)
              exact hP1.trans hP2
            have hP2 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP3 : (𝒢ᵣ' |ₕ [u ∶ E :: Γ']) |ₕ [x ∶ B :: Δ] |ₕ
                [x' ∶ A :: Γ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
                [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              conv_rhs => rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP2.trans ((HyperEnv.Perm.merge (by rfl) hP1).trans hP3)
          have hPΓ'' : Γ'' ~ Γ' := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢_mem : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢_mem))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | h
              · exact hux (by rfl)
              · have h_in_x_block : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) h_in_x_block hFu
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | h
              · exact hux' (by rfl)
              · have h_in_x_block : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) h_in_x_block hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE').mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
          have hPΔ'' : Δ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
            have hin_v : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hin_v
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hv𝒢_mem : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢_mem))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx (by rfl)
              · have h_in_x_block : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) h_in_x_block hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx' (by rfl)
              · have hCell : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvΓ' (Env.mem_pair_fst_in_names _ h)
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
              [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hP3 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP1) hP2
            exact hP3.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have hP_final : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Γ' ++ Ξᵣ] := by
            have : [Γ''‚ Δ''] ~ [y' ∶ C :: y ∶ D :: Γ' ++ Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have h2 : Γ' ++ y' ∶ C :: y ∶ D :: Ξᵣ ~ y' ∶ C :: y ∶ D :: Γ' ++ Ξᵣ :=
                (List.perm_middle).trans (List.Perm.cons _ (List.perm_middle))
              exact (List.Perm.append hPΓ'' hPΔ'').trans h2
            exact HyperEnv.Perm.merge (by rfl) this
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
  · rcases hEv with hv𝒢 | rfl | rfl
    · left
      obtain ⟨𝒢ᵣ', hP𝒢ᵣ'⟩ := HyperEnv.exists_perm_cons_of_mem hv𝒢
      have huin := (List.Perm.mem_iff (a := u ∶ E) hPEu.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_append] at huin
      rcases huin with ⟨rfl, _⟩ | huΓ | huΔ
      · exfalso ; exact hux (by rfl)
      · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (u, E) :: Γᵣ := Env.exists_perm_cons huΓ
        have hPΓ' : Γ' ~ x ∶ A ⨂ B :: Γᵣ ++ Δ := by
          have h1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append hPΓ (List.Perm.refl Δ)))
          exact ((hPEu.symm.trans h1).trans (List.Perm.swap ..)).cons_inv
        refine ⟨𝒢ᵣ', Γᵣ ++ Δ', Δ, Ξ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEu
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP_final : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [Γ'‚ Δ'] ~
            𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: (Γᵣ ++ Δ') ++ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have hP1 : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: (Γᵣ ++ Δ') ++ Δ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have : ((x ∶ A ⨂ B :: Γᵣ)‚ Δ)‚ Δ' ~ (x ∶ A ⨂ B :: (Γᵣ‚ Δ'))‚ Δ := by
                rw [← List.cons_append]
                simp only [Env.merge]
                rw [List.append_assoc, List.append_assoc]
                apply List.Perm.append (by rfl) (List.perm_append_comm)
              exact (List.Perm.append hPΓ' (List.Perm.refl Δ')).trans this
            have hP2 : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [x ∶ A ⨂ B :: (Γᵣ ++ Δ') ++ Δ] ~
              𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: (Γᵣ ++ Δ') ++ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans hP2
          exact (HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans hP_final
        · have h𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
                HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
              have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
                rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
              exact hP𝒢ᵣ'.trans (hP1.trans hP2)
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
              have hP2 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP31 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_rotate_rhs_left
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rfl
                have hP32 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] ~
                  (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                exact hP31.trans hP32
              exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append] ; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : [x' ∶ A :: Γ] ~ [u ∶ E :: x' ∶ A :: Γᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x' ∶ A) hPΓ).trans (List.Perm.swap ..)
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] |ₕ
                [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP31 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] |ₕ
                  [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                (𝒢ᵣ' |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                  [y' ∶ C :: y ∶ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP32 : (𝒢ᵣ' |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                  [y' ∶ C :: y ∶ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                  [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                rfl
              exact hP31.trans hP32
            exact hP1.trans ((((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl))).trans hP3)
          have hPΓ'' : Γ'' ~ x' ∶ A :: Γᵣ := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢_mem : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢_mem))
            · exfalso
              have hP1 : ℋ |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                have : [x ∶ B :: Δ] ~ [u ∶ E :: Γ''] :=
                  HyperEnv.Perm_singleton_singleton.mpr hPE'
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) this) (by rfl)
              have hP2 : ℋ |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                (ℋ |ₕ [v ∶ Eᗮ :: Δ'']) |ₕ [x ∶ B :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP3 : 𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                  [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                  [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] := by
                conv_lhs => rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_right
                simp only [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP4 := (hP2.symm.trans (hP1.trans h_post_subst)).trans hP3
              apply HyperEnv.Perm_merge_cancel_right at hP4
              have hin : (u ∶ E :: x' ∶ A :: Γᵣ) ∈
                𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                  [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP4 hin
              simp only [List.mem_append, List.mem_singleton] at hE1
              rcases hE1 with hℋ | rfl
              · have huE1 : (u, E) ∈ E1 := (List.Perm.mem_iff hPE1.symm).mp (by simp)
                exact hFu' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ huE1))
              · have hinu' : (v, Eᗮ) ∈ u ∶ E :: x' ∶ A :: Γᵣ :=
                  (List.Perm.mem_iff hPE1).mp (by simp)
                simp at hinu'
                rcases hinu' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv.symm (by rfl)
                · exact hvx' (by rfl)
                · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hCell : (u, E) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact huΔ' (Env.mem_pair_fst_in_names _ h)
          have hPΔ'' : Δ'' ~ Δ' := by
            have hin_v : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hin_v
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hv𝒢_mem : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢_mem))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | hΔ
              · exact hvx (by rfl)
              · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [hΔ])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hCell : (v, Eᗮ) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvx' (by rfl)
              · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have h1 : [u ∶ E :: Γ''] ~ [u ∶ E :: x' ∶ A :: Γᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have h2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) h1) h2
            exact hLHS.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have hP_final : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γᵣ ++ Δ'] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
            have hP1 : [Γ''‚ Δ''] ~ [x' ∶ A :: Γᵣ ++ Δ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have h1 := List.Perm.append hPΓ'' hPΔ''
              have h2 : x' ∶ A :: Γᵣ ++ Δ' ~ x' ∶ A :: Γᵣ ++ Δ' := List.Perm.refl _
              exact h1.trans h2
            have hP2 : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [x' ∶ A :: Γᵣ ++ Δ'] ~
              𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γᵣ ++ Δ'] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_merge_cancel_right_inv
              rfl
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans hP2
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
      · obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (u, E) :: Δᵣ := Env.exists_perm_cons huΔ
        have hPΓ' : Γ' ~ x ∶ A ⨂ B :: Γ ++ Δᵣ := by
          have hP1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append (List.Perm.refl Γ) hPΔ))
          have hP2 : Γ ++ (u, E) :: Δᵣ ~ (u, E) :: Γ ++ Δᵣ := List.perm_middle
          have hP3 := List.Perm.cons (x ∶ A ⨂ B) hP2
          exact ((hPEu.symm.trans hP1).trans (hP3.trans (List.Perm.swap ..))).cons_inv
        refine ⟨𝒢ᵣ', Γ, (Δᵣ‚ Δ'), Ξ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEu
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP_final : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [Γ'‚ Δ'] ~
            𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ (Δᵣ ++ Δ')] |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have hP1 : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γ‚ (Δᵣ ++ Δ')] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP11 := List.Perm.append hPΓ' (List.Perm.refl Δ')
              have hP12 : (x ∶ A ⨂ B :: Γ ++ Δᵣ) ++ Δ' ~ x ∶ A ⨂ B :: Γ ++ Δᵣ ++ Δ' := by
                rw [List.cons_append]
              conv_rhs at hP12 => rw [List.append_assoc]
              exact hP11.trans hP12
            have hP2 : (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [x ∶ A ⨂ B :: Γ‚ (Δᵣ ++ Δ')] ~
              𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ (Δᵣ ++ Δ')] |ₕ [y ∶ C ⅋ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans hP2
          exact (HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans hP_final
        · have h𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by
            have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
                HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
              have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
                rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
              exact hP𝒢ᵣ'.trans (hP1.trans hP2)
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
              have hP2 : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP31 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_rotate_rhs_left
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rfl
                have hP32 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [y ∶ C ⅋ D :: Ξ] |ₕ [u ∶ E :: Γ'] ~
                  (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                exact hP31.trans hP32
              exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).trans hP3)
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append] ; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : [x ∶ B :: Δ] ~ [u ∶ E :: x ∶ B :: Δᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x ∶ B) hPΔ).trans (List.Perm.swap ..)
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP31 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                  [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                (𝒢ᵣ' |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                  [y' ∶ C :: y ∶ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                conv_rhs => rw [← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP32 : (𝒢ᵣ' |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                  [y' ∶ C :: y ∶ D :: Ξ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
                  [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                rfl
              exact hP31.trans hP32
            exact hP1.trans
              ((((HyperEnv.Perm.merge (by rfl) hP2).merge (by rfl)).merge (by rfl)).trans hP3)
          have hPΓ'' : Γ'' ~ x ∶ B :: Δᵣ := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hu𝒢_mem : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢_mem))
            · exfalso
              have hP1 : ℋ |ₕ [x' ∶ A :: Γ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                have : [x' ∶ A :: Γ] ~ [u ∶ E :: Γ''] :=
                  HyperEnv.Perm_singleton_singleton.mpr hPE'
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) this) (by rfl)
              have hP2 : ℋ |ₕ [x' ∶ A :: Γ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                (ℋ |ₕ [v ∶ Eᗮ :: Δ'']) |ₕ [x' ∶ A :: Γ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP3 : 𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ
                  [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] ~
                (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                  [v ∶ Eᗮ :: Δ']) |ₕ [x' ∶ A :: Γ] := by
                conv_lhs => rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_right
                simp only [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP4 := (hP2.symm.trans (hP1.trans h_post_subst)).trans hP3
              apply HyperEnv.Perm_merge_cancel_right at hP4
              have hin : (u ∶ E :: x ∶ B :: Δᵣ) ∈
                𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP4 hin
              simp only [List.mem_append, List.mem_singleton] at hE1
              rcases hE1 with hℋ | rfl
              · have huE1 : (u, E) ∈ E1 := (List.Perm.mem_iff hPE1.symm).mp (by simp)
                exact hFu' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ huE1))
              · have hinu' : (v, Eᗮ) ∈ u ∶ E :: x ∶ B :: Δᵣ :=
                  (List.Perm.mem_iff hPE1).mp (by simp)
                simp at hinu'
                rcases hinu' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv.symm (by rfl)
                · exact hvx (by rfl)
                · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huy' (by rfl)
              · exact huy (by rfl)
              · have hCell : (u, E) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact huΔ' (Env.mem_pair_fst_in_names _ h)
          have hPΔ'' : Δ'' ~ Δ' := by
            have hin_v : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hin_v
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ' | rfl | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              have hE'RHS : E' ∈ 𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Ξ] := by simp [h𝒢ᵣ']
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 hE'RHS
              have hv𝒢_mem : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢_mem))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | hΓ
              · exact hvx' (by rfl)
              · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [hΓ])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hCell : (v, Eᗮ) ∈ y ∶ C ⅋ D :: Ξ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE').mpr (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvx (by rfl)
              · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ
              [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have h1 : [u ∶ E :: Γ''] ~ [u ∶ E :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have h2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) h1) h2
            exact hLHS.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have hP_final : (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Δᵣ ++ Δ'] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
            have hP1 : [Γ''‚ Δ''] ~ [x ∶ B :: Δᵣ ++ Δ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have h1 := List.Perm.append hPΓ'' hPΔ''
              have h2 : x ∶ B :: Δᵣ ++ Δ' ~ x ∶ B :: Δᵣ ++ Δ' := List.Perm.refl _
              exact h1.trans h2
            have hP2 : (𝒢ᵣ' |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ]) |ₕ [x ∶ B :: Δᵣ ++ Δ'] ~
              𝒢ᵣ' |ₕ [x ∶ B :: Δᵣ ++ Δ'] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_rotate_rhs_right
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rfl
            exact (HyperEnv.Perm.merge (by rfl) hP1).trans hP2
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
    · exfalso
      have hPEuv : u ∶ E :: Γ' ~ v ∶ Eᗮ :: Δ' := hPEu.symm.trans hPEv
      have huin' : (u, E) ∈ v ∶ Eᗮ :: Δ' := (List.Perm.mem_iff hPEuv).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq] at huin'
      rcases huin' with ⟨rfl, _⟩ | hΔ'
      · exact huv (by rfl)
      · exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
    · right
      have huin := (List.Perm.mem_iff (a := u ∶ E) hPEu.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_append] at huin
      rcases huin with ⟨rfl, _⟩ | huΓ | huΔ
      · exfalso ; exact hux (by rfl)
      · have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPEv.symm).mp (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at hvin
        rcases hvin with ⟨rfl, _⟩ | hvΞ
        · exfalso ; exact hvy (by rfl)
        · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (u, E) :: Γᵣ := Env.exists_perm_cons huΓ
          obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (v, Eᗮ) :: Ξᵣ := Env.exists_perm_cons hvΞ
          have hPΓ' : Γ' ~ x ∶ A ⨂ B :: Γᵣ ++ Δ := by
            have h1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append hPΓ (List.Perm.refl Δ)))
            exact ((hPEu.symm.trans h1).trans (List.Perm.swap ..)).cons_inv
          have hPΔ' : Δ' ~ y ∶ C ⅋ D :: Ξᵣ := by
            have h1 := hPEv.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
            exact (h1.trans (List.Perm.swap ..)).cons_inv
          refine ⟨𝒢ᵣ, Γᵣ, Δ, Ξᵣ, ?_, ?_⟩
          · have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPx) (by rfl)
                have hP2 : 𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] :=
                  HyperEnv.Perm.merge (by rfl) hPy
                exact h_pre.trans (hP1.trans hP2)
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hP_tail : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γᵣ‚ Δ ++ y ∶ C ⅋ D :: Ξᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.append hPΓ' hPΔ')
            have := HyperEnv.Perm.merge h𝒢 (HyperEnv.Perm.refl [Γ'‚ Δ'])
            exact this.trans (HyperEnv.Perm.merge (by rfl) hP_tail)
          · left
            have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have h1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPx) (by rfl)
                have h2 : 𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] :=
                  HyperEnv.Perm.merge (by rfl) hPy
                exact h_pre.trans (h1.trans h2)
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hPu : [x' ∶ A :: Γ] ~ [u ∶ E :: x' ∶ A :: Γᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x' ∶ A) hPΓ).trans (List.Perm.swap ..)
            have hPv : [y' ∶ C :: y ∶ D :: Ξ] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP1 := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
              have hP2 : y' ∶ C :: y ∶ D :: (v, Eᗮ) :: Ξᵣ ~ (v, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ := by
                have : y' ∶ C :: y ∶ D :: (v, Eᗮ) :: Ξᵣ ~
                  y' ∶ C :: (v, Eᗮ) :: y ∶ D :: Ξᵣ := List.Perm.cons _ (List.Perm.swap ..)
                exact this.trans (List.Perm.swap ..)
              exact hP1.trans hP2
            have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have hP1 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
                apply HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPu) (by rfl)
              have hP2 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                  [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm.merge (by rfl) hPv
              exact h_post.trans (hP1.trans hP2)
            have hPΓ'' : Γ'' ~ x' ∶ A :: Γᵣ := by
              have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ| rfl | rfl | rfl
              · exfalso
                have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ
                have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
                exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
              · exfalso
                have hP1 : ℋ |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                  ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                  have : [x ∶ B :: Δ] ~ [u ∶ E :: Γ''] :=
                    HyperEnv.Perm_singleton_singleton.mpr hPE'
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) this) (by rfl)
                have hP2 : ℋ |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                  (ℋ |ₕ [v ∶ Eᗮ :: Δ'']) |ₕ [x ∶ B :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  exact HyperEnv.Perm.merge (HyperEnv.Perm.merge_comm) (by rfl)
                have hP3 : (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                    [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  (𝒢ᵣ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                    [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [x ∶ B :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                have hP4 := (hP2.symm.trans (hP1.trans h_post_subst)).trans hP3
                apply HyperEnv.Perm_merge_cancel_right at hP4
                have hin : (u ∶ E :: x' ∶ A :: Γᵣ) ∈
                  𝒢ᵣ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by simp
                obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP4 hin
                simp only [List.mem_append, List.mem_singleton] at hE1
                rcases hE1 with hℋ | rfl
                · have huE : (u, E) ∈ E1 := (List.Perm.mem_iff hPE1).mpr (by simp)
                  exact hFu' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ huE))
                · have hvinu' : (v, Eᗮ) ∈ u ∶ E :: x' ∶ A :: Γᵣ :=
                    (List.Perm.mem_iff hPE1).mp (by simp)
                  simp at hvinu'
                  rcases hvinu' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                  · exact huv.symm (by rfl)
                  · exact hvx' (by rfl)
                  · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
              · exact List.Perm.cons_inv hPE'.symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
                simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv (by rfl)
                · exact huy' (by rfl)
                · exact huy (by rfl)
                · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                  exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            have hPΔ'' : Δ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
              have hin_v : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hin_v
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ_mem | rfl | rfl | rfl
              · exfalso
                have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ_mem
                have hv𝒢_mem : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
                exact hFv
                  (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢_mem))
              · exfalso
                have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
                simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
                · exact hvx (by rfl)
                · have h_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ h_Γ')
              · exfalso
                have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
                simp at hvin ; rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv.symm (by rfl)
                · exact hvx' (by rfl)
                · have h_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ h_Γ')
              · exact List.Perm.cons_inv hPE'.symm
            have hP_post : ℋ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: x' ∶ A :: Γᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
              have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
              have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ E :: x' ∶ A :: Γᵣ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hP1) hP2
              exact hLHS.symm.trans h_post_subst
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            have hP_final : (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [Γ''‚ Δ''] ~
              𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have : [Γ''‚ Δ''] ~ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact List.Perm.append hPΓ'' hPΔ''
              exact HyperEnv.Perm.merge (by rfl) this
            exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
      · have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPEv.symm).mp (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at hvin
        rcases hvin with ⟨rfl, _⟩ | hvΞ
        · exfalso ; exact hvy (by rfl)
        · obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (u, E) :: Δᵣ := Env.exists_perm_cons huΔ
          obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (v, Eᗮ) :: Ξᵣ := Env.exists_perm_cons hvΞ
          have hPΓ' : Γ' ~ x ∶ A ⨂ B :: Γ ++ Δᵣ := by
            have h1 := (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append (List.Perm.refl Γ) hPΔ))
            have h2 : Γ ++ (u, E) :: Δᵣ ~ (u, E) :: Γ ++ Δᵣ := List.perm_middle
            have h3 := List.Perm.cons (x ∶ A ⨂ B) h2
            exact ((hPEu.symm.trans h1).trans (h3.trans (List.Perm.swap ..))).cons_inv
          have hPΔ' : Δ' ~ y ∶ C ⅋ D :: Ξᵣ := by
            have h1 := hPEv.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
            exact (h1.trans (List.Perm.swap ..)).cons_inv
          refine ⟨𝒢ᵣ, Γ, Δᵣ, Ξᵣ, ?_, ?_⟩
          · have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPx) (by rfl)
                have hP2 : 𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] :=
                  HyperEnv.Perm.merge (by rfl) hPy
                exact h_pre.trans (hP1.trans hP2)
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hP_tail : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact List.Perm.append hPΓ' hPΔ'
            exact (HyperEnv.Perm.merge h𝒢 (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans
              (HyperEnv.Perm.merge (by rfl) hP_tail)
          · right
            have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [y ∶ C ⅋ D :: Ξ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPx) (by rfl)
                have hP2 : 𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] :=
                  HyperEnv.Perm.merge (by rfl) hPy
                exact h_pre.trans (hP1.trans hP2)
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hPu : [x ∶ B :: Δ] ~ [u ∶ E :: x ∶ B :: Δᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x ∶ B) hPΔ).trans (List.Perm.swap ..)
            have hPv : [y' ∶ C :: y ∶ D :: Ξ] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP1 := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
              have hP2 : y' ∶ C :: y ∶ D :: (v, Eᗮ) :: Ξᵣ ~ (v, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ := by
                exact (List.Perm.cons _ (List.Perm.swap ..)).trans (List.Perm.swap ..)
              exact hP1.trans hP2
            have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have hP1 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] := by
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hP2 : 𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPu) (by rfl)
              have hP3 : 𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                  [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm.merge (by rfl) hPv
              exact h_post.trans (hP1.trans (hP2.trans hP3))
            have hPΓ'' : Γ'' ~ x ∶ B :: Δᵣ := by
              have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ | rfl | rfl | rfl
              · exfalso
                have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ
                have hu𝒢_mem : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
                exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢_mem))
              · exfalso
                have hP1 : ℋ |ₕ [x' ∶ A :: Γ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                  ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                  have := HyperEnv.Perm_singleton_singleton.mpr hPE'.symm
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) (this).symm) (by rfl)
                have hP2 : ℋ |ₕ [x' ∶ A :: Γ] |ₕ [v ∶ Eᗮ :: Δ''] ~
                  (ℋ |ₕ [v ∶ Eᗮ :: Δ'']) |ₕ [x' ∶ A :: Γ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  exact HyperEnv.Perm_merge_cancel_right_inv HyperEnv.Perm.merge_comm
                have hP3 : (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                    [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  (𝒢ᵣ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
                    [x' ∶ A :: Γ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                have hP4 := (hP2.symm.trans (hP1.trans h_post_subst)).trans hP3
                apply HyperEnv.Perm_merge_cancel_right at hP4
                have hin : (u ∶ E :: x ∶ B :: Δᵣ) ∈
                  𝒢ᵣ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by simp
                obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP4 hin
                simp only [List.mem_append, List.mem_singleton] at hE1
                rcases hE1 with hℋ | rfl
                · have huE1 : (u, E) ∈ E1 := (List.Perm.mem_iff hPE1).mpr (by simp)
                  exact hFu' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ huE1))
                · have hvinu' : (v, Eᗮ) ∈ u ∶ E :: x ∶ B :: Δᵣ :=
                    (List.Perm.mem_iff hPE1).mp (by simp)
                  simp at hvinu'
                  rcases hvinu' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                  · exact huv.symm (by rfl)
                  · exact hvx (by rfl)
                  · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
              · exact List.Perm.cons_inv hPE'.symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
                simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv (by rfl)
                · exact huy' (by rfl)
                · exact huy (by rfl)
                · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                  exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            have hPΔ'' : Δ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
              have hinv' : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ | rfl | rfl | rfl
              · exfalso
                have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ
                have hv𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
                exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢))
              · exfalso
                have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
                simp at hvin
                rcases hvin with ⟨rfl, _⟩ | h
                · exact hvx' (by rfl)
                · have h_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ h_Γ')
              · exfalso
                have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
                simp at hvin
                rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv.symm (by rfl)
                · exact hvx (by rfl)
                · have h_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ h_Γ')
              · exact List.Perm.cons_inv hPE'.symm
            have hP_post : ℋ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ
                [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: x ∶ B :: Δᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
              have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
              have hP3 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ E :: x ∶ B :: Δᵣ] |ₕ [v ∶ Eᗮ :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hP1) hP2
              exact hP3.symm.trans h_post_subst
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            have hP_final : (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [Γ''‚ Δ''] ~
              𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have : [Γ''‚ Δ''] ~ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact (List.Perm.append hPΓ'' hPΔ'')
              exact HyperEnv.Perm.merge (by rfl) this
            exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
  · rcases hEv with hv𝒢 | rfl | rfl
    · left
      obtain ⟨𝒢ᵣ', hP𝒢ᵣ'⟩ := HyperEnv.exists_perm_cons_of_mem hv𝒢
      have huin := (List.Perm.mem_iff (a := u ∶ E) hPEu.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq] at huin
      rcases huin with ⟨rfl, _⟩ | huΞ
      · exfalso ; exact huy (by rfl)
      · obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (u, E) :: Ξᵣ := Env.exists_perm_cons huΞ
        have hPΓ' : Γ' ~ y ∶ C ⅋ D :: Ξᵣ := by
          have h1 := hPEu.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
          exact (h1.trans (List.Perm.swap ..)).cons_inv
        refine ⟨𝒢ᵣ', Γ, Δ, Δ' ++ Ξᵣ, ?_, ?_⟩
        · have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have h_pre_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
            have hP2 : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEu
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [u ∶ E :: Γ'] ~
              (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans (((HyperEnv.Perm.merge (by rfl) hP2)).trans hP3)
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          have hP_final : (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [Γ'‚ Δ'] ~
            𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Δ' ++ Ξᵣ] := by
            have hP1 : [Γ'‚ Δ'] ~ [y ∶ C ⅋ D :: Δ' ++ Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP11 := List.Perm.append hPΓ' (List.Perm.refl Δ')
              have hP12 : y ∶ C ⅋ D :: Ξᵣ ++ Δ' ~ y ∶ C ⅋ D :: Δ' ++ Ξᵣ :=
                List.Perm.cons _ List.perm_append_comm
              exact hP11.trans hP12
            exact HyperEnv.Perm.merge (by rfl) hP1
          exact (HyperEnv.Perm.merge h_pre_subst (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans hP_final
        · have h𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by
            have h𝒢ᵣ_split : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
                HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
              have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
                rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
              exact hP𝒢ᵣ'.trans (hP1.trans hP2)
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 := h_pre.trans ((h𝒢ᵣ_split.merge (by rfl)).merge (by rfl))
              have hP2 : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [u ∶ E :: Γ'] ~
                (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact hP1.trans ((HyperEnv.Perm.merge (by rfl) hP2).trans hP3)
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have h𝒢ᵣ_split_post : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : Ev :: 𝒢ᵣ' ~ (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' :=
              HyperEnv.Perm.cons hPEv (HyperEnv.Perm.refl _)
            have hP2 : (v ∶ Eᗮ :: Δ') :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ'] := by
              rw [HyperEnv.cons_append]; apply HyperEnv.Perm.merge_comm
            exact hP𝒢ᵣ'.trans (hP1.trans hP2)
          have hPy' : [y' ∶ C :: y ∶ D :: Ξ] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have h1 := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
            have h2 : y' ∶ C :: y ∶ D :: (u, E) :: Ξᵣ ~ (u, E) :: y' ∶ C :: y ∶ D :: Ξᵣ :=
              (List.Perm.cons _ (List.Perm.swap ..)).trans (List.Perm.swap ..)
            exact h1.trans h2
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
              [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 := h_post.trans
              ((((h𝒢ᵣ_split_post.merge (by rfl)).merge (by rfl)).merge (by rfl)))
            have hP2 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] |ₕ
                [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ
                [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] := HyperEnv.Perm.merge (by rfl) hPy'
            have hP3 : (𝒢ᵣ' |ₕ [v ∶ Eᗮ :: Δ']) |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ
              [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
                [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact hP1.trans (hP2.trans hP3)
          have hPΓ'' : Γ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ | rfl | rfl | rfl | rfl
            · exfalso
              have h𝒢ᵣx : E' ∈ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp [h𝒢ᵣ]
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣx
              have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux (by rfl)
              · have hCell : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact hux' (by rfl)
              · have hCell : (u, E) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFu
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin
              rcases huin with ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact huΔ' (Env.mem_pair_fst_in_names _ h)
          have hPΔ'' : Δ'' ~ Δ' := by
            have hinv' : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ | rfl | rfl | rfl | rfl
            · exfalso
              have h𝒢ᵣx : E' ∈ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp [h𝒢ᵣ]
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣx
              have hv𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx (by rfl)
              · have hCell : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx' (by rfl)
              · have hCell : (v, Eᗮ) ∈ x ∶ A ⨂ B :: Γ‚ Δ := by simp [h]
                exact HyperEnv.absurd_fresh_of_mem_perm h𝒢 (by simp) hCell hFv
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv.symm (by rfl)
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hΓ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [h])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hΓ')
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ
              [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: Δ'] := by
            have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hP3 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hP1) hP2
            exact hP3.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have hP_final : (𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ' |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Δ' ++ Ξᵣ] := by
            have hP1 : [Γ''‚ Δ''] ~ [y' ∶ C :: y ∶ D :: Δ' ++ Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hP11 := List.Perm.append hPΓ'' hPΔ''
              have hP12 : y' ∶ C :: y ∶ D :: Ξᵣ ++ Δ' ~ y' ∶ C :: y ∶ D :: Δ' ++ Ξᵣ := by
                simp only [List.cons_append]
                apply List.Perm.cons
                apply List.Perm.cons
                apply List.perm_append_comm
              exact hP11.trans hP12
            exact HyperEnv.Perm.merge (by rfl) hP1
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
    · right
      have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPEv.symm).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_append] at hvin
      rcases hvin with ⟨rfl, _⟩ | hvΓ | hvΔ
      · exfalso ; exact hvx (by rfl)
      · have huin := (List.Perm.mem_iff (a := u ∶ E) hPEu.symm).mp (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at huin
        rcases huin with ⟨rfl, _⟩ | huΞ
        · exfalso ; exact huy (by rfl)
        · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (v, Eᗮ) :: Γᵣ := Env.exists_perm_cons hvΓ
          obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (u, E) :: Ξᵣ := Env.exists_perm_cons huΞ
          have hPΔ' : Δ' ~ x ∶ A ⨂ B :: Γᵣ ++ Δ := by
            have h1 := hPEv.symm.trans
              (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append hPΓ (List.Perm.refl Δ)))
            exact (h1.trans (List.Perm.swap ..)).cons_inv
          have hPΓ' : Γ' ~ y ∶ C ⅋ D :: Ξᵣ := by
            have h1 := hPEu.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
            exact (h1.trans (List.Perm.swap ..)).cons_inv
          refine ⟨𝒢ᵣ, Γᵣ, Δ, Ξᵣ, ?_, ?_⟩
          · have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPy) (by rfl)
                have hP2 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] :=
                  HyperEnv.Perm.merge (by rfl) hPx
                have hP3 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                exact h_pre.trans (hP1.trans (hP2.trans hP3))
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hP_tail : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γᵣ‚ Δ ++ y ∶ C ⅋ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have h1 := List.Perm.append hPΓ' hPΔ'
              have h2 : y ∶ C ⅋ D :: Ξᵣ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δ) ~
                x ∶ A ⨂ B :: Γᵣ‚ Δ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.trans List.perm_append_comm
                rfl
              exact h1.trans h2
            exact (h𝒢.merge (by rfl)).trans (HyperEnv.Perm.merge (by rfl) hP_tail)
          · left
            have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
              have hPx : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEu
              have hPy : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
                HyperEnv.Perm_singleton_singleton.mpr hPEv
              have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                  𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPy) (by rfl)
                have hP2 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~ 𝒢ᵣ |ₕ
                  [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] := HyperEnv.Perm.merge (by rfl) hPx
                have hP3 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] ~
                  𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                exact h_pre.trans (hP1.trans (hP2.trans hP3))
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              apply HyperEnv.Perm_merge_cancel_right at h_subst
              exact h_subst
            have hPu : [y' ∶ C :: y ∶ D :: Ξ] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
              exact this.trans ((List.Perm.cons _ (List.Perm.swap ..)).trans (List.Perm.swap ..))
            have hPv : [x' ∶ A :: Γ] ~ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons (x' ∶ A) hPΓ).trans (List.Perm.swap ..)
            have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
              have hP1 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
                𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [x' ∶ A :: Γ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm.merge ?_ hPu
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_rotate_rhs_left
                rfl
              have hP2 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [x' ∶ A :: Γ] ~
                (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                  [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] :=
                HyperEnv.Perm.merge (by rfl) hPv
              exact h_post.trans (hP1.trans hP2)
            have hPΓ'' : Γ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
              have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ | rfl | rfl | rfl
              · exfalso
                have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ
                have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
                exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
                simp at huin ; rcases huin with ⟨rfl, _⟩ | h
                · exact hux (by rfl)
                · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                  exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
              · exact List.Perm.cons_inv hPE'.symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
                simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact huv (by rfl)
                · exact hux' (by rfl)
                · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                  exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            have hPΔ'' : Δ'' ~ x' ∶ A :: Γᵣ := by
              have hinv' : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
              obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
              rcases hE' with h𝒢ᵣ | rfl | rfl | rfl
              · exfalso
                have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
                obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ
                have hv𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
                exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢))
              · exfalso
                have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
                simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
                · exact hvx (by rfl)
                · exfalso
                  have hP1 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [x ∶ B :: Δ] ~
                    ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                    have : [x ∶ B :: Δ] ~ [v ∶ Eᗮ :: Δ''] :=
                      HyperEnv.Perm_singleton_singleton.mpr hPE'
                    HyperEnv.Perm.merge (by rfl) this
                  have hP2 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                      [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] ~
                    (𝒢ᵣ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ]) |ₕ
                      [x ∶ B :: Δ] := by
                    conv_lhs => rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                    apply HyperEnv.Perm_rotate_rhs_right
                    simp only [← HyperEnv.merge_assoc]
                    apply HyperEnv.Perm_merge_cancel_right_inv
                    apply HyperEnv.Perm_merge_cancel_right_inv
                    exact HyperEnv.Perm.merge_comm
                  have hP3 := (hP1.trans h_post_subst).trans hP2
                  apply HyperEnv.Perm_merge_cancel_right at hP3
                  have hin : (v ∶ Eᗮ :: x' ∶ A :: Γᵣ) ∈
                    𝒢ᵣ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by simp
                  obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP3 hin
                  simp only [List.mem_append, List.mem_singleton] at hE1
                  rcases hE1 with hℋ | rfl
                  · have hvE : (v, Eᗮ) ∈ E1 := (List.Perm.mem_iff hPE1).mpr (by simp)
                    have hE1Names := Env.mem_pair_fst_in_names _ hvE
                    exact hFv' (HyperEnv.subset_names_of_mem hℋ hE1Names)
                  · have huinv' : (u, E) ∈ v ∶ Eᗮ :: x' ∶ A :: Γᵣ :=
                      (List.Perm.mem_iff hPE1).mp (by simp)
                    simp at huinv'
                    rcases huinv' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                    · exact huv (by rfl)
                    · exact hux' (by rfl)
                    · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                      exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
              · exfalso
                have hvin' : (v, Eᗮ) ∈ u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ :=
                  (List.Perm.mem_iff hPE').mpr (by simp)
                simp at hvin'
                rcases hvin' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hv_Ξᵣ
                · exact huv.symm (by rfl)
                · exact hvy' (by rfl)
                · exact hvy (by rfl)
                · have hv_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [hv_Ξᵣ])
                  exact hvΓ' (Env.mem_pair_fst_in_names _ hv_Γ')
              · exact List.Perm.cons_inv hPE'.symm
            have hP_post : ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] ~
              (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] := by
              have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
              have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] :=
                HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
              have hLHS : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x' ∶ A :: Γᵣ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hP1) hP2
              exact hLHS.symm.trans h_post_subst
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            apply HyperEnv.Perm_merge_cancel_right at hP_post
            have hP_final : (𝒢ᵣ |ₕ [x ∶ B :: Δ]) |ₕ [Γ''‚ Δ''] ~
              𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have : [Γ''‚ Δ''] ~ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                rw [HyperEnv.Perm_singleton_singleton]
                have h1 := List.Perm.append hPΓ'' hPΔ''
                have h2 : y' ∶ C :: y ∶ D :: Ξᵣ ++ x' ∶ A :: Γᵣ ~
                  x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                  apply List.Perm.trans List.perm_append_comm
                  rfl
                exact h1.trans h2
              exact HyperEnv.Perm.merge (by rfl) this
            exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
      · have huiny' := (List.Perm.mem_iff (a := u ∶ E) hPEu.symm).mp (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at huiny'
        rcases huiny' with ⟨rfl, _⟩ | huΞ
        · exfalso ; exact huy (by rfl)
        obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (v, Eᗮ) :: Δᵣ := Env.exists_perm_cons hvΔ
        obtain ⟨Ξᵣ, hPΞ⟩ : ∃ Ξᵣ, Ξ ~ (u, E) :: Ξᵣ := Env.exists_perm_cons huΞ
        have hPΓ' : Γ' ~ y ∶ C ⅋ D :: Ξᵣ := by
          have h1 := hPEu.symm.trans (List.Perm.cons (y ∶ C ⅋ D) hPΞ)
          exact (h1.trans (List.Perm.swap ..)).cons_inv
        have hPΔ' : Δ' ~ x ∶ A ⨂ B :: Γ ++ Δᵣ := by
          have h1 := hPEv.symm.trans
            (List.Perm.cons (x ∶ A ⨂ B) (List.Perm.append (List.Perm.refl Γ) hPΔ))
          have h2 : Γ ++ (v, Eᗮ) :: Δᵣ ~ (v, Eᗮ) :: Γ ++ Δᵣ := List.perm_middle
          have h3 := List.Perm.cons (x ∶ A ⨂ B) h2
          exact ((h1.trans (h3.trans (List.Perm.swap ..)))).cons_inv
        refine ⟨𝒢ᵣ, Γ, Δᵣ, Ξᵣ, ?_, ?_⟩
        · have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
            have hPx : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEu
            have hPy : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEv
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPy) (by rfl)
              have hP2 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] :=
                HyperEnv.Perm.merge (by rfl) hPx
              have hP3 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] ~
                𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact h_pre.trans (hP1.trans (hP2.trans hP3))
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have hP_tail : [Γ'‚ Δ'] ~ [x ∶ A ⨂ B :: Γ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hP1 := List.Perm.append hPΓ' hPΔ'
            have hP2 : (y ∶ C ⅋ D :: Ξᵣ) ++ (x ∶ A ⨂ B :: Γ ++ Δᵣ) ~
              (x ∶ A ⨂ B :: Γ ++ Δᵣ) ++ (y ∶ C ⅋ D :: Ξᵣ) := List.perm_append_comm
            have hP3 : (x ∶ A ⨂ B :: Γ ++ Δᵣ) ++ (y ∶ C ⅋ D :: Ξᵣ) =
              x ∶ A ⨂ B :: Γ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              rw [List.append_assoc]
            rw [hP3] at hP2
            exact hP1.trans hP2
          exact (HyperEnv.Perm.merge h𝒢
            (HyperEnv.Perm.refl [Γ'‚ Δ'])).trans (HyperEnv.Perm.merge (by rfl) hP_tail)
        · right
          have h𝒢 : 𝒢 ~ 𝒢ᵣ := by
            have hPx : [y ∶ C ⅋ D :: Ξ] ~ [u ∶ E :: Γ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEu
            have hPy : [x ∶ A ⨂ B :: Γ‚ Δ] ~ [v ∶ Eᗮ :: Δ'] :=
              HyperEnv.Perm_singleton_singleton.mpr hPEv
            have h_subst : 𝒢 |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] ~
              𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
              have hP1 : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPy) (by rfl)
              have hP2 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [y ∶ C ⅋ D :: Ξ] ~
                𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] :=
                HyperEnv.Perm.merge (by rfl) hPx
              have hP3 : 𝒢ᵣ |ₕ [v ∶ Eᗮ :: Δ'] |ₕ [u ∶ E :: Γ'] ~
                 𝒢ᵣ |ₕ [u ∶ E :: Γ'] |ₕ [v ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact h_pre.trans (hP1.trans (hP2.trans hP3))
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_subst
            exact h_subst
          have hPu : [y' ∶ C :: y ∶ D :: Ξ] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have h1 := List.Perm.cons (y' ∶ C) (List.Perm.cons (y ∶ D) hPΞ)
            exact h1.trans ((List.Perm.cons _ (List.Perm.swap ..)).trans (List.Perm.swap ..))
          have hPv : [x ∶ B :: Δ] ~ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            exact (List.Perm.cons (x ∶ B) hPΔ).trans (List.Perm.swap ..)
          have h_post_subst : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
            (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
              [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
            have hP1 : 𝒢ᵣ |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] ~
              𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [x ∶ B :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have hP2 : 𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ C :: y ∶ D :: Ξ] |ₕ [x ∶ B :: Δ] ~
              𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [x ∶ B :: Δ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPu) (by rfl)
            have hP3 : 𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [x ∶ B :: Δ] ~
              (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [v ∶ Eᗮ :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm.merge (by rfl) hPv
            exact h_post.trans (hP1.trans (hP2.trans hP3))
          have hPΓ'' : Γ'' ~ y' ∶ C :: y ∶ D :: Ξᵣ := by
            have hinu' : (u ∶ E :: Γ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinu'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ_mem | rfl | rfl | rfl
            · exfalso
              have huE' : (u, E) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ_mem
              have hu𝒢 : (u, E) ∈ E'' := (List.Perm.mem_iff hPE'').mpr huE'
              exact hFu (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hu𝒢))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | h
              · exact hux' (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            · exact List.Perm.cons_inv hPE'.symm
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ E) hPE'.symm).mp (by simp)
              simp at huin ; rcases huin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
              · exact huv (by rfl)
              · exact hux (by rfl)
              · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
          have hPΔ'' : Δ'' ~ x ∶ B :: Δᵣ := by
            have hinv' : (v ∶ Eᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] := by simp
            obtain ⟨E', hE', hPE'⟩ := HyperEnv.Perm_mem h_post_subst.symm hinv'
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE'
            rcases hE' with h𝒢ᵣ_mem | rfl | rfl | rfl
            · exfalso
              have hvE' : (v, Eᗮ) ∈ E' := (List.Perm.mem_iff hPE').mpr (by simp)
              obtain ⟨E'', hE'', hPE''⟩ := HyperEnv.Perm_mem h𝒢 h𝒢ᵣ_mem
              have hv𝒢 : (v, Eᗮ) ∈ E'' := (List.Perm.mem_iff hPE'').mpr hvE'
              exact hFv (HyperEnv.subset_names_of_mem hE'' (Env.mem_pair_fst_in_names _ hv𝒢))
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Eᗮ) hPE'.symm).mp (by simp)
              simp at hvin ; rcases hvin with ⟨rfl, _⟩ | h
              · exact hvx' (by rfl)
              · exfalso
                have hP1 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [x' ∶ A :: Γ] ~
                  ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] :=
                  have : [x' ∶ A :: Γ] ~ [v ∶ Eᗮ :: Δ''] :=
                    HyperEnv.Perm_singleton_singleton.mpr hPE'
                  HyperEnv.Perm.merge (by rfl) this
                have hP2 : 𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                    [v ∶ Eᗮ :: x ∶ B :: Δᵣ] ~
                  (𝒢ᵣ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                    [v ∶ Eᗮ :: x ∶ B :: Δᵣ]) |ₕ [x' ∶ A :: Γ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                have hP3 := (hP1.trans h_post_subst).trans hP2
                apply HyperEnv.Perm_merge_cancel_right at hP3
                have hin : (v ∶ Eᗮ :: x ∶ B :: Δᵣ) ∈
                  𝒢ᵣ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by simp
                obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP3 hin
                simp only [List.mem_append, List.mem_singleton] at hE1
                rcases hE1 with hℋ | rfl
                · have hvE : (v, Eᗮ) ∈ E1 := (List.Perm.mem_iff hPE1).mpr (by simp)
                  exact hFv' (HyperEnv.subset_names_of_mem hℋ (Env.mem_pair_fst_in_names _ hvE))
                · have huinv' : (u, E) ∈ v ∶ Eᗮ :: x ∶ B :: Δᵣ :=
                    (List.Perm.mem_iff hPE1).mp (by simp)
                  simp at huinv'
                  rcases huinv' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                  · exact huv (by rfl)
                  · exact hux (by rfl)
                  · have hΔ' : (u, E) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [h])
                    exact huΔ' (Env.mem_pair_fst_in_names _ hΔ')
            · exfalso
              have hvin1 : (v, Eᗮ) ∈ u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ :=
                (List.Perm.mem_iff hPE').mpr (by simp)
              simp at hvin1
              rcases hvin1 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hv_Ξᵣ
              · exact huv.symm (by rfl)
              · exact hvy' (by rfl)
              · exact hvy (by rfl)
              · have hv_Γ' : (v, Eᗮ) ∈ Γ' := (List.Perm.mem_iff hPΓ').mpr (by simp [hv_Ξᵣ])
                exact hvΓ' (Env.mem_pair_fst_in_names _ hv_Γ')
            · exact List.Perm.cons_inv hPE'.symm
          have hP_post : ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] ~
            (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
              [v ∶ Eᗮ :: x ∶ B :: Δᵣ] := by
            have hP1 : [u ∶ E :: Γ''] ~ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ'')
            have hP2 : [v ∶ Eᗮ :: Δ''] ~ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ'')
            have hP3 : ℋ |ₕ [u ∶ E :: Γ''] |ₕ [v ∶ Eᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ E :: y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [v ∶ Eᗮ :: x ∶ B :: Δᵣ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hP1) hP2
            exact hP3.symm.trans h_post_subst
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          apply HyperEnv.Perm_merge_cancel_right at hP_post
          have hP_final : (𝒢ᵣ |ₕ [x' ∶ A :: Γ]) |ₕ [Γ''‚ Δ''] ~
            𝒢ᵣ |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have : [Γ''‚ Δ''] ~ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have : y' ∶ C :: y ∶ D :: Ξᵣ ++ x ∶ B :: Δᵣ ~
                x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                apply List.Perm.trans List.perm_append_comm
                rfl
              exact (List.Perm.append hPΓ'' hPΔ'').trans this
            exact HyperEnv.Perm.merge (by rfl) this
          exact (HyperEnv.Perm.merge hP_post (HyperEnv.Perm.refl [Γ''‚ Δ''])).trans hP_final
    · exfalso
      have hPEuv : u ∶ E :: Γ' ~ v ∶ Eᗮ :: Δ' := hPEu.symm.trans hPEv
      have hu_in : (u, E) ∈ v ∶ Eᗮ :: Δ' := (List.Perm.mem_iff hPEuv).mp (by simp)
      simp only [List.mem_cons, Prod.mk.injEq] at hu_in
      rcases hu_in with ⟨rfl, _⟩ | h
      · exact huv (by rfl)
      · exact huΔ' (Env.mem_pair_fst_in_names _ h)
