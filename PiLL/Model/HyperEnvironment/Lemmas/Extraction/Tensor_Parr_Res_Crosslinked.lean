import PiLL.Model.HyperEnvironment.Lemmas.Basic

lemma HyperEnv.Perm.extract_tensor_parr_res_crosslinked
  {𝒢 𝒢' 𝒢ᵣ : HyperEnv} {Γ Δ Γ' Δ' Γᵣ Δᵣ : Env} {Ξᵣ : List Elem}
  {A B C D E : Types} {z w x x' y y' : FPName}
  (hP_pre : 𝒢 |ₕ [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] ~
    𝒢ᵣ |ₕ [(x ∶ A ⨂ B :: Γᵣ‚ Δᵣ)‚ (y ∶ C ⅋ D :: Ξᵣ)])
  (hP_post : (𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
      𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] |ₕ [(x' ∶ A :: Γᵣ)‚ (y' ∶ C :: y ∶ D :: Ξᵣ)]) ∨
    (𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
      𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] |ₕ [(x ∶ B :: Δᵣ)‚ (y' ∶ C :: y ∶ D :: Ξᵣ)]))
  (hzx' : z ≠ x') (hzy' : z ≠ y') (hwx' : w ≠ x') (hwy' : w ≠ y')
  (hzx : z ≠ x) (hwx : w ≠ x) (hwy : w ≠ y) (hzy : z ≠ y) (hzw : z ≠ w)
  (hz𝒢 : z ∉ 𝒢.names) (hz𝒢' : z ∉ 𝒢'.names) (hw𝒢 : w ∉ 𝒢.names) (hw𝒢' : w ∉ 𝒢'.names)
  (hzΓ : z ∉ Γ.names) (hzΓ' : z ∉ Γ'.names) (hzΔ : z ∉ Δ.names) (hzΔ' : z ∉ Δ'.names)
  (hwΓ : w ∉ Γ.names) (hwΓ' : w ∉ Γ'.names) (hwΔ : w ∉ Δ.names) (hwΔ' : w ∉ Δ'.names) :
  ∃ 𝒢ₙ Γₙ Δₙ Ξₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ₙ |ₕ [(x ∶ A ⨂ B :: Γₙ‚ Δₙ)‚ (y ∶ C ⅋ D :: Ξₙ)] ∧
    ((𝒢' |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ B :: Δₙ] |ₕ [(x' ∶ A :: Γₙ)‚ (y' ∶ C :: y ∶ D :: Ξₙ)]) ∨
     (𝒢' |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x' ∶ A :: Γₙ] |ₕ [(x ∶ B :: Δₙ)‚ (y' ∶ C :: y ∶ D :: Ξₙ)])) := by
  have hxin : ((x ∶ A ⨂ B :: Γᵣ‚ Δᵣ)‚ (y ∶ C ⅋ D :: Ξᵣ)) ∈
    𝒢ᵣ |ₕ [(x ∶ A ⨂ B :: Γᵣ‚ Δᵣ)‚ (y ∶ C ⅋ D :: Ξᵣ)] := by simp
  obtain ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem hP_pre hxin
  simp only [List.mem_append, List.mem_singleton, or_assoc] at hE1
  rcases hE1 with hx𝒢 | rfl | rfl
  · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hx𝒢
    have hP𝒢 : 𝒢 ~ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
      have h1 : E1 :: 𝒢ᵣ' ~ 𝒢ᵣ' |ₕ [E1] := by
        rw [HyperEnv.cons_append]
        exact HyperEnv.Perm.merge_comm
      have h2 : 𝒢ᵣ' |ₕ [E1] ~ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] :=
        HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hPE1)
      exact h𝒢_split.trans (h1.trans h2)
    obtain ⟨hz𝒢ᵣ', hzx, hzΓᵣ, hzΔᵣ, hzy, hzΞᵣ⟩ := by
      rw [HyperEnv.names_eq_of_perm hP𝒢] at hz𝒢
      simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Finset.notMem_union,
        Env.names_merge, Env.names_distributes, Finset.notMem_singleton, and_assoc] at hz𝒢
      exact hz𝒢
    obtain ⟨hw𝒢ᵣ', hwx, hwΓᵣ, hwΔᵣ, hwy, hwΞᵣ⟩ := by
      rw [HyperEnv.names_eq_of_perm hP𝒢] at hw𝒢
      simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Finset.notMem_union,
        Env.names_merge, Env.names_distributes, Finset.notMem_singleton, and_assoc] at hw𝒢
      exact hw𝒢
    have h_pre_subst : (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ
        [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] ~
      𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
      have hP1 : 𝒢 |ₕ [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] ~
        (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ]) |ₕ [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] :=
        HyperEnv.Perm.merge (HyperEnv.Perm.merge hP𝒢 (by rfl)) (by rfl)
      have hP2 : (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ])
          |ₕ [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] ~
        (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        rw [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_right_inv
        exact HyperEnv.Perm.merge_comm
      exact (hP1.trans hP2).symm.trans hP_pre
    apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
    refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Γᵣ, Δᵣ, Ξᵣ, ?_, ?_⟩
    · have this : (𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ]) |ₕ [Γ‚ Δ] ~
        (𝒢ᵣ' |ₕ [Γ‚ Δ]) |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ] := by
        conv_rhs => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_comm_assoc_rhs
        conv_rhs => rw [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_left
        rfl
      exact (HyperEnv.Perm.merge hP𝒢 (by rfl)).trans this
    · rcases hP_post with hPost1 | hPost2
      · left
        have hPost1' : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] := by
          have hP11 : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
            (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ [x ∶ B :: Δᵣ] |ₕ
              [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge h_pre_subst.symm (by rfl)) (by rfl)
          have hP12 : (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ [x ∶ B :: Δᵣ] |ₕ
              [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
            (𝒢ᵣ' |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] := by
            conv_rhs => rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_merge_cancel_right_inv
            apply HyperEnv.Perm_rotate_rhs_right
            rfl
          exact hPost1.trans (hP11.trans hP12)
        have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
          have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
          obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem hPost1'.symm hin
          simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
          rcases hE2 with hE2𝒢ᵣ' | rfl | rfl | rfl | rfl
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            exact hz𝒢ᵣ' (HyperEnv.mem_of_mem_mem_names hinE2 hE2𝒢ᵣ')
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzx (by rfl)
            · exact hzΔᵣ (Env.mem_pair_fst_in_names _ h)
          · have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h2
            · exfalso ; exact hzx' (by rfl)
            · exfalso ; exact hzΓᵣ (Env.mem_pair_fst_in_names _ h1)
            · exfalso ; exact hzy' (by rfl)
            · exfalso ; exact hzy (by rfl)
            · exfalso ; exact hzΞᵣ (Env.mem_pair_fst_in_names _ h2)
          · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzw (by rfl)
            · exact hzΔ (Env.mem_pair_fst_in_names _ h)
        have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
          have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
          obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem hPost1'.symm hin
          simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
          rcases hE2 with hE2𝒢ᵣ' | rfl | rfl | rfl | rfl
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            exact hw𝒢ᵣ' (HyperEnv.mem_of_mem_mem_names hinE2 hE2𝒢ᵣ')
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hwx (by rfl)
            · exact hwΔᵣ (Env.mem_pair_fst_in_names _ h)
          · have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h2
            · exfalso ; exact hwx' (by rfl)
            · exfalso ; exact hwΓᵣ (Env.mem_pair_fst_in_names _ h1)
            · exfalso ; exact hwy' (by rfl)
            · exfalso ; exact hwy (by rfl)
            · exfalso ; exact hwΞᵣ (Env.mem_pair_fst_in_names _ h2)
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzw (by rfl)
            · exact hwΓ (Env.mem_pair_fst_in_names _ h)
          · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
        have hPost_final : 𝒢' |ₕ [Γ'‚ Δ'] ~ (𝒢ᵣ' |ₕ [Γ‚ Δ]) |ₕ [x ∶ B :: Δᵣ] |ₕ
          [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
          have hP1 := (HyperEnv.Perm.merge
            (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ').symm.trans hPost1'
          apply HyperEnv.Perm_merge_cancel_right at hP1
          apply HyperEnv.Perm_merge_cancel_right at hP1
          have hP2 : [Γ'‚ Δ'] ~ [Γ‚ Δ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hP21 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
            have hP22 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
            exact List.Perm.append hP21 hP22
          have hP3 : (𝒢ᵣ' |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [Γ‚ Δ] ~
            (𝒢ᵣ' |ₕ [Γ‚ Δ]) |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            conv_rhs => rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            rfl
          exact (HyperEnv.Perm.merge hP1 (by rfl)).trans
            ((HyperEnv.Perm.merge (by rfl) hP2).trans hP3)
        exact hPost_final
      · right
        have hPost2' : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] := by
          have hP1 : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
            (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ [x' ∶ A :: Γᵣ] |ₕ
              [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge h_pre_subst.symm (by rfl)) (by rfl)
          have hP2 : (𝒢ᵣ' |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: Δ] |ₕ [x' ∶ A :: Γᵣ] |ₕ
              [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
            (𝒢ᵣ' |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] := by
            conv_rhs => rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            conv_rhs => rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_merge_cancel_right_inv
            apply HyperEnv.Perm_rotate_rhs_right
            rfl
          exact hPost2.trans (hP1.trans hP2)
        have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
          have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
          obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem hPost2'.symm hin
          simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
          rcases hE2 with hE2𝒢ᵣ' | rfl | rfl | rfl | rfl
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            exact hz𝒢ᵣ' (HyperEnv.mem_of_mem_mem_names hinE2 hE2𝒢ᵣ')
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzx' (by rfl)
            · exact hzΓᵣ (Env.mem_pair_fst_in_names _ h)
          · have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h2
            · exfalso ; exact hzx (by rfl)
            · exfalso ; exact hzΔᵣ (Env.mem_pair_fst_in_names _ h1)
            · exfalso ; exact hzy' (by rfl)
            · exfalso ; exact hzy (by rfl)
            · exfalso ; exact hzΞᵣ (Env.mem_pair_fst_in_names _ h2)
          · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzw (by rfl)
            · exact hzΔ (Env.mem_pair_fst_in_names _ h)
        have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
          have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
          obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem hPost2'.symm hin
          simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
          rcases hE2 with hE2𝒢ᵣ' | rfl | rfl | rfl | rfl
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            exact hw𝒢ᵣ' (HyperEnv.mem_of_mem_mem_names hinE2 hE2𝒢ᵣ')
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hwx' (by rfl)
            · exact hwΓᵣ (Env.mem_pair_fst_in_names _ h)
          · have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h2
            · exfalso ; exact hwx (by rfl)
            · exfalso ; exact hwΔᵣ (Env.mem_pair_fst_in_names _ h1)
            · exfalso ; exact hwy' (by rfl)
            · exfalso ; exact hwy (by rfl)
            · exfalso ; exact hwΞᵣ (Env.mem_pair_fst_in_names _ h2)
          · exfalso
            have hinE2 := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
            simp at hinE2
            rcases hinE2 with ⟨rfl, _⟩ | h
            · exact hzw (by rfl)
            · exact hwΓ (Env.mem_pair_fst_in_names _ h)
          · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
        have hP_post_final : 𝒢' |ₕ [Γ'‚ Δ'] ~ (𝒢ᵣ' |ₕ [Γ‚ Δ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ
            [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
          have hP1 := (HyperEnv.Perm.merge
            (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ').symm.trans hPost2'
          apply HyperEnv.Perm_merge_cancel_right at hP1
          apply HyperEnv.Perm_merge_cancel_right at hP1
          have hP2 : [Γ'‚ Δ'] ~ [Γ‚ Δ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            exact List.Perm.append
              (List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ'))
              (List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ'))
          have hP3 : (𝒢ᵣ' |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [Γ‚ Δ] ~
            (𝒢ᵣ' |ₕ [Γ‚ Δ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            apply HyperEnv.Perm_rotate_rhs_left
            rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_merge_cancel_right_inv
            apply HyperEnv.Perm_rotate_rhs_right
            rfl
          exact (HyperEnv.Perm.merge hP1 (by rfl)).trans
            ((HyperEnv.Perm.merge (by rfl) hP2).trans hP3)
        exact hP_post_final
  · have hzin := (List.Perm.mem_iff (a :=  (z, E)) hPE1).mp (by simp)
    simp only [List.cons_append, List.append_assoc, List.mem_cons, Prod.mk.injEq,
      List.mem_append] at hzin
    have hP𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [w ∶ Eᗮ :: Δ] := by
      have : 𝒢 |ₕ [z ∶ E :: Γ] |ₕ [w ∶ Eᗮ :: Δ] ~
        𝒢 |ₕ [(x ∶ A ⨂ B :: Γᵣ‚ Δᵣ)‚ (y ∶ C ⅋ D :: Ξᵣ)] |ₕ [w ∶ Eᗮ :: Δ] := by
        apply HyperEnv.Perm_merge_cancel_right_inv
        apply HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hPE1)
      have := hP_pre.symm.trans this
      apply HyperEnv.Perm_merge_cancel_right (𝒥 := [(x ∶ A ⨂ B :: Γᵣ‚ Δᵣ)‚ (y ∶ C ⅋ D :: Ξᵣ)])
      conv_rhs => rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_comm_assoc_rhs
      conv_rhs => rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_left
      exact this
    rcases hzin with ⟨rfl, _⟩ | h1 | h2 | ⟨rfl, _⟩ | h3
    · exfalso ; exact hzx (by rfl)
    · obtain ⟨Γᵣ', hPΓᵣ⟩ := Env.exists_perm_cons h1
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ' ++ Δ, Δᵣ, Ξᵣ, ?_, ?_⟩
        · have hP : Γ ++ Δ ~ x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.cons
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                have hP21 : x ∶ A ⨂ B :: (Γᵣ' ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) ++ Δ ~
                    x ∶ A ⨂ B :: Γᵣ' ++ ((Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ) := by
                    apply List.Perm.cons
                    simp only [List.append_eq, List.append_assoc, List.cons_append, List.Perm.refl]
                have hP22 : x ∶ A ⨂ B :: Γᵣ' ++ ((Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ) ~
                    x ∶ A ⨂ B :: Γᵣ' ++ (Δ ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) :=
                    List.Perm.append (List.Perm.refl _) (List.perm_append_comm)
                have hP23 : x ∶ A ⨂ B :: Γᵣ' ++ (Δ ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) ~
                    x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                    apply List.Perm.cons
                    simp only [← List.append_assoc, List.append_eq, List.Perm.refl]
                rw [List.cons_append, List.cons_append, List.append_assoc, List.cons_append]
                conv_rhs => rw [List.append_assoc]
                exact hP21.trans (hP22.trans hP23)
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hP)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: (Γᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  x ∶ A ⨂ B :: (z, E) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                  apply List.Perm.cons
                  simp only [List.append_eq, List.append_assoc, List.cons_append]
                  simp only [← List.append_assoc, ← List.cons_append]
                  apply List.Perm.append ?_ (by rfl)
                  apply List.Perm.append hPΓᵣ (by rfl)
                exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
              have hzΔᵣ : z ∉ Δᵣ.names := by
                intro h
                have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                  simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                  right ; right ; right ; left ; exact h
                exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
              have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                  (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                    [w ∶ Eᗮ :: Δ] := by
                have hP1 : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                    [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                  rw [HyperEnv.Perm_singleton_singleton]
                  exact (List.Perm.cons _ (List.Perm.append hPΓᵣ (List.Perm.refl _))).trans
                    (List.Perm.swap ..)
                have hP2 : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x ∶ B :: Δᵣ] |ₕ
                    [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ
                    [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [w ∶ Eᗮ :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  rw [← HyperEnv.merge_assoc]
                  apply HyperEnv.Perm_merge_cancel_right_inv
                  exact HyperEnv.Perm.merge_comm
                exact (hPostL.trans
                  (HyperEnv.Perm.merge (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl)) hP1)).trans hP2
              have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
                obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
                simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
                rcases hE2 with h𝒢 | rfl | rfl | rfl
                · exfalso
                  have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                  exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hzE2))
                · exfalso
                  have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                  simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                  · exact hzx (by rfl)
                  · exact hzΔᵣ (Env.mem_pair_fst_in_names _ hz_in)
                · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
                · exfalso
                  have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                  simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                  · exact hzw (by rfl)
                  · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
              have hnwin : w ∉ Env.names (z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) := by
                intro h
                simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                  Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                  Finset.mem_union] at h
                rcases h with rfl | rfl | rfl | rfl | h4 | h5
                · exact hwy (by rfl)
                · exact hwy' (by rfl)
                · exact hwx' (by rfl)
                · exact hzw (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; left ; exact h4
                  exact hwΓ hΓ
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; right ; exact h5
                  exact hwΓ hΓ
              have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
                have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
                obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
                simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
                rcases hE2 with h𝒢 | rfl | rfl | rfl | h4 | h5 | h6
                · exfalso
                  have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                  exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
                · exfalso
                  have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                  simp at hwin ; rcases hwin with ⟨rfl, _⟩ | h
                  · exact hwx (by rfl)
                  · exfalso
                    have hΓ : w ∈ Γ.names := by
                      rw [Env.names_eq_of_perm hP1]
                      simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                        Env.names_merge, Finset.singleton_union, Finset.union_insert,
                        Finset.mem_insert, Finset.mem_union]
                      right ; right ; right ; left ; exact Env.mem_pair_fst_in_names _ h
                    exact hwΓ hΓ
                · exfalso
                  have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                  apply hnwin (Env.mem_pair_fst_in_names _ hwin)
                · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              have hP1 : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                  𝒢' |ₕ [z ∶ E :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [w ∶ Eᗮ :: Δ] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
              have hP2 := hP1.symm.trans h_subst
              apply HyperEnv.Perm_merge_cancel_right at hP2
              apply HyperEnv.Perm_merge_cancel_right at hP2
              have hP_tail : [Γ'‚ Δ'] ~ [x' ∶ A :: (Γᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                rw [HyperEnv.Perm_singleton_singleton]
                have hP1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
                have hP2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
                have hP3 : (x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ++ Δ ~
                    x' ∶ A :: (Γᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                  rw [List.cons_append]
                  apply List.Perm.cons
                  have hP4 : (Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ++ Δ ~
                    Γᵣ' ++ (y' ∶ C :: y ∶ D :: Ξᵣ ++ Δ) := by rw [List.append_assoc]
                  have hP5 : Γᵣ' ++ (y' ∶ C :: y ∶ D :: Ξᵣ ++ Δ) ~
                    Γᵣ' ++ (Δ ++ y' ∶ C :: y ∶ D :: Ξᵣ) :=
                    List.Perm.append (by rfl) List.perm_append_comm
                  have hP6 : Γᵣ' ++ (Δ ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                    (Γᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by rw [← List.append_assoc]
                  exact hP4.trans (hP5.trans hP6)
                exact (List.Perm.append hP1 hP2).trans hP3
              exact HyperEnv.Perm.merge hP2 hP_tail
          exact hP
      · refine ⟨𝒢, Γᵣ' ++ Δ, Δᵣ, Ξᵣ, ?_, ?_⟩
        · have hP : Γ ++ Δ ~ x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.cons
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have hP21 : x ∶ A ⨂ B :: (Γᵣ' ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) ++ Δ ~
                  x ∶ A ⨂ B :: Γᵣ' ++ ((Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ) := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append, List.Perm.refl]
              have hP22 : x ∶ A ⨂ B :: Γᵣ' ++ ((Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ) ~
                  x ∶ A ⨂ B :: Γᵣ' ++ (Δ ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) :=
                List.Perm.append (List.Perm.refl _) (List.perm_append_comm)
              have hP23 : x ∶ A ⨂ B :: Γᵣ' ++ (Δ ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ)) ~
                  x ∶ A ⨂ B :: (Γᵣ' ++ Δ) ++ (Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                apply List.Perm.cons
                simp only [← List.append_assoc, List.append_eq, List.Perm.refl]
              rw [List.cons_append, List.cons_append, List.append_assoc, List.cons_append]
              conv_rhs => rw [List.append_assoc]
              exact hP21.trans (hP22.trans hP23)
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hP)
        · right
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x' ∶ A :: (Γᵣ' ++ Δ)] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append]
                simp only [← List.append_assoc, ← List.cons_append]
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hzΔᵣ : z ∉ Δᵣ.names := by
              intro h
              have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; right ; left ; exact h
              exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
            have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
              (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ'] |ₕ
                [w ∶ Eᗮ :: Δ] := by
              have hp_z_block : [x' ∶ A :: Γᵣ] ~ [z ∶ E :: x' ∶ A :: Γᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact (List.Perm.cons _ hPΓᵣ).trans (List.Perm.swap ..)
              have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                  (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ'] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ hp_z_block)
              have h_mid := HyperEnv.Perm.merge hp_left
                (by rfl : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~ _)
              have h_rot : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ'] |ₕ
                  [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_left
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_left
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact (hPostR.trans h_mid).trans h_rot
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x' ∶ A :: Γᵣ'] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin
                rcases hzin with ⟨rfl, _⟩ | h
                · exact hzx (by rfl)
                · have hz_not : z ∉ (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                    intro hz
                    simp only [Env.names_merge, Env.names_distributes, Finset.singleton_union,
                      Finset.union_insert, Finset.mem_insert, Finset.mem_union] at hz
                    rcases hz with rfl | rfl | hΔᵣ | hΞᵣ
                    · exact hzy (by rfl)
                    · exact hzy' (by rfl)
                    · have hΓ : z ∈ Γ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                          Env.names_merge, Finset.singleton_union, Finset.union_insert,
                          Finset.mem_insert, Finset.mem_union]
                        right ; right ; right ; left ; exact hΔᵣ
                      exact hzΓ hΓ
                    · have hΓ : z ∈ Γ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                          Env.names_merge, Finset.singleton_union, Finset.union_insert,
                          Finset.mem_insert, Finset.mem_union]
                        right ; right ; right ; right ; exact hΞᵣ
                      exact hzΓ hΓ
                  rcases h with hΔᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                  · exact hzΔᵣ (Env.mem_pair_fst_in_names _ hΔᵣ)
                  · exact hzy' (by rfl)
                  · exact hzy (by rfl)
                  · apply hz_not
                    simp only [Env.names_merge, Env.names_distributes, Finset.singleton_union,
                      Finset.union_insert, Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzw (by rfl)
                · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
            have hnwin : w ∉ Env.names (z ∶ E :: x' ∶ A :: Γᵣ') := by
              intro h
              simp only [Env.names_distributes, Finset.singleton_union,
                Finset.union_insert, Finset.mem_insert] at h
              rcases h with rfl | rfl | hΓᵣ
              · exact hwx' (by rfl)
              · exact hzw (by rfl)
              · have hΓ : w ∈ Γ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union]
                  right ; right ; left ; exact hΓᵣ
                exact hwΓ hΓ
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp only [List.cons_append, List.mem_cons, Prod.mk.injEq, List.mem_append] at hwin
                rcases hwin with ⟨rfl, _⟩ | hΔᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                · exact hwx (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΔᵣ
                  exact hwΓ hΓ
                · exact hwy' (by rfl)
                · exact hwy (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; right ; exact Env.mem_pair_fst_in_names _ hΞᵣ
                  exact hwΓ hΓ
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                exact hnwin (Env.mem_pair_fst_in_names _ hwin)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have h_LHS_perm : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                𝒢' |ₕ [z ∶ E :: x' ∶ A :: Γᵣ'] |ₕ [w ∶ Eᗮ :: Δ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~ [x' ∶ A :: (Γᵣ' ++ Δ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              have h_rearrange : (x' ∶ A :: Γᵣ') ++ Δ ~ x' ∶ A :: (Γᵣ' ++ Δ) := by
                rw [List.cons_append]
              exact h_app.trans h_rearrange
            have h_merged := HyperEnv.Perm.merge h_cancel h_tail
            have h_rot2 : (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [x' ∶ A :: (Γᵣ' ++ Δ)] ~
              𝒢 |ₕ [x' ∶ A :: (Γᵣ' ++ Δ)] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_merged.trans h_rot2
          exact hP
    · obtain ⟨Δᵣ', hPΔᵣ⟩ := Env.exists_perm_cons h2
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ, Δᵣ' ++ Δ, Ξᵣ, ?_, ?_⟩
        · have hP : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  rw [List.append_assoc, List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                    (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
              apply List.Perm.cons
              have s1 : (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                Γᵣ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ++ Δ) := by
                rw [List.append_assoc, List.append_assoc, List.append_assoc]
              have s2 : Γᵣ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ++ Δ) ~
                Γᵣ ++ (Δᵣ' ++ (Δ ++ y ∶ C ⅋ D :: Ξᵣ)) := by
                apply List.Perm.append (by rfl)
                rw [List.append_assoc]
                apply List.Perm.append (by rfl)
                rw [List.append_cons, List.cons_append]
                have : y ∶ C ⅋ D :: (Ξᵣ ++ Δ) = (y ∶ C ⅋ D :: Ξᵣ) ++ Δ := by rfl
                rw [this, List.append_assoc]
                apply List.perm_append_comm
              have s3 : Γᵣ ++ (Δᵣ' ++ (Δ ++ y ∶ C ⅋ D :: Ξᵣ)) ~
                Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                repeat rw [← List.append_assoc]
              exact s1.trans (s2.trans s3)
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hP)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: (Δᵣ' ++ Δ)] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  rw [List.append_assoc, List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                    (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hzΓᵣ : z ∉ Γᵣ.names := by
              intro h
              have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; left ; exact h
              exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
            have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
              have hp_z_block : [x ∶ B :: Δᵣ] ~ [z ∶ E :: x ∶ B :: Δᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact (List.Perm.cons _ hPΔᵣ).trans (List.Perm.swap ..)
              have hp_left : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] ~
                  (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ'] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ hp_z_block)
              have h_mid := HyperEnv.Perm.merge hp_left
                (by rfl : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~ _)
              have h_rot : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ'] |ₕ
                  [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_left
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_left
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact (hPostL.trans h_mid).trans h_rot
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x ∶ B :: Δᵣ'] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzx' (by rfl)
                · have hz_not : z ∉ (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                    intro hz
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union] at hz
                    rcases hz with rfl | rfl | hΓᵣ | hΞᵣ
                    · exact hzy (by rfl)
                    · exact hzy' (by rfl)
                    · exact hzΓᵣ hΓᵣ
                    · have hΓ : z ∈ Γ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc,
                          Env.names_distributes, Env.names_merge, Finset.singleton_union,
                            Finset.union_insert, Finset.mem_insert, Finset.mem_union]
                        right ; right ; right ; right ; exact hΞᵣ
                      exact hzΓ hΓ
                  rcases hz_in with hΓᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                  · exact hzΓᵣ (Env.mem_pair_fst_in_names _ hΓᵣ)
                  · exact hzy' (by rfl)
                  · exact hzy (by rfl)
                  · apply hz_not
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert,
                        Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzw (by rfl)
                · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
            have hnwin : w ∉ Env.names (z ∶ E :: x ∶ B :: Δᵣ') := by
              intro h
              simp only [Env.names_distributes, Finset.singleton_union,
                Finset.union_insert, Finset.mem_insert] at h
              rcases h with rfl | rfl | hΔᵣ
              · exact hwx (by rfl)
              · exact hzw (by rfl)
              · have hΓ : w ∈ Γ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  right ; right ; right ; left ; exact hΔᵣ
                exact hwΓ hΓ
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp only [List.cons_append, List.mem_cons, Prod.mk.injEq, List.mem_append] at hwin
                rcases hwin with ⟨rfl, _⟩ | hΓᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                · exact hwx' (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΓᵣ
                  exact hwΓ hΓ
                · exact hwy' (by rfl)
                · exact hwy (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; right ; exact Env.mem_pair_fst_in_names _ hΞᵣ
                  exact hwΓ hΓ
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                exact hnwin (Env.mem_pair_fst_in_names _ hwin)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have h_LHS_perm : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                𝒢' |ₕ [z ∶ E :: x ∶ B :: Δᵣ'] |ₕ [w ∶ Eᗮ :: Δ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: (Δᵣ' ++ Δ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              have h_rearrange : (x ∶ B :: Δᵣ') ++ Δ ~ x ∶ B :: (Δᵣ' ++ Δ) := by
                rw [List.cons_append]
              exact h_app.trans h_rearrange
            have h_merged := HyperEnv.Perm.merge h_cancel h_tail
            have h_rot2 : (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [x ∶ B :: (Δᵣ' ++ Δ)] ~
              𝒢 |ₕ [x ∶ B :: (Δᵣ' ++ Δ)] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_merged.trans h_rot2
          exact hP
      · have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
          𝒢 |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: (Δᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
          have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
            have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
              x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              apply List.Perm.cons
              have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                repeat rw [List.append_assoc]
                apply List.Perm.append (by rfl)
                apply List.Perm.append hPΔᵣ (by rfl)
              have s2 : Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                  (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                exact List.Perm.append List.perm_middle (List.Perm.refl _)
              exact s1.trans s2
            exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
          have hzΓᵣ : z ∉ Γᵣ.names := by
            intro h
            have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
              simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
              right ; right ; left ; exact h
            exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
          have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
            (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
              [w ∶ Eᗮ :: Δ] := by
            have hp_z_block : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have s1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                  x ∶ B :: (z, E) :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                apply List.Perm.cons
                exact List.Perm.append hPΔᵣ (List.Perm.refl _)
              exact s1.trans (List.Perm.swap ..)
            have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x' ∶ A :: Γᵣ] :=
              (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
            have h_mid := HyperEnv.Perm.merge hp_left hp_z_block
            have h_rot : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ
                [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [w ∶ Eᗮ :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact (hPostR.trans h_mid).trans h_rot
          have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                (Env.mem_pair_fst_in_names _ hzE2))
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
              · exact hzx' (by rfl)
              · exact hzΓᵣ (Env.mem_pair_fst_in_names _ hz_in)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
              · exact hzw (by rfl)
              · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
          have hnwin : w ∉ Env.names (z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) := by
            intro h
            simp only [List.cons_append, Env.names_distributes, Env.names_merge,
              Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
              Finset.mem_union] at h
            rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΔhΞᵣ
            · exact hwy (by rfl)
            · exact hwy' (by rfl)
            · exact hwx (by rfl)
            · exact hzw (by rfl)
            · exfalso
              have hΓ : w ∈ Γ.names := by
                rw [Env.names_eq_of_perm hP1]
                simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                  Env.names_merge, Finset.singleton_union, Finset.union_insert,
                  Finset.mem_insert, Finset.mem_union]
                right ; right ; right ; exact hΔhΞᵣ
              exact hwΓ hΓ
          have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
            have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp only [List.mem_cons, Prod.mk.injEq] at hwin
              rcases hwin with ⟨rfl, _⟩ | hΓᵣ
              · exact hwx' (by rfl)
              · have hΓ : w ∈ Γ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΓᵣ
                exact hwΓ hΓ
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              exact hnwin (Env.mem_pair_fst_in_names _ hwin)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          have h_LHS_perm : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
              𝒢' |ₕ [z ∶ E :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [w ∶ Eᗮ :: Δ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
          have h_cancel := h_LHS_perm.symm.trans h_subst
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: (Δᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
            have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
            have h_app := List.Perm.append hp1 hp2
            have h_rearrange : (x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ++ Δ ~
                x ∶ B :: (Δᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
              rw [List.cons_append]
              apply List.Perm.cons
              have s1 : (Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ++ Δ ~
                  Δᵣ' ++ (y' ∶ C :: y ∶ D :: Ξᵣ ++ Δ) := by rw [List.append_assoc]
              have s2 : Δᵣ' ++ (y' ∶ C :: y ∶ D :: Ξᵣ ++ Δ) ~
                  Δᵣ' ++ (Δ ++ y' ∶ C :: y ∶ D :: Ξᵣ) :=
                List.Perm.append (by rfl) List.perm_append_comm
              have s3 : Δᵣ' ++ (Δ ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                  (Δᵣ' ++ Δ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by rw [← List.append_assoc]
              exact s1.trans (s2.trans s3)
            exact h_app.trans h_rearrange
          have h_merged := HyperEnv.Perm.merge h_cancel h_tail
          exact h_merged
        refine ⟨𝒢, Γᵣ, Δᵣ' ++ Δ, Ξᵣ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (z, E) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                    (z, E) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
              apply List.Perm.cons
              have s1 : (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ++ Δ ~
                  Γᵣ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ++ Δ) := by
                  repeat rw [List.append_assoc]
              have s2 : Γᵣ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ++ Δ) ~
                Γᵣ ++ (Δᵣ' ++ (Δ ++ y ∶ C ⅋ D :: Ξᵣ)) := by
                repeat rw [List.append_assoc]
                exact List.Perm.append (by rfl)
                  (List.Perm.append (by rfl) List.perm_append_comm)
              have s3 : Γᵣ ++ (Δᵣ' ++ (Δ ++ y ∶ C ⅋ D :: Ξᵣ)) ~
                Γᵣ ++ (Δᵣ' ++ Δ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                repeat rw [← List.append_assoc]
              exact s1.trans (s2.trans s3)
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · right ; exact hP
    · exfalso ; exact hzy (by rfl)
    · obtain ⟨Ξᵣ', hPΞᵣ⟩ := Env.exists_perm_cons h3
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ, Δᵣ, Ξᵣ' ++ Δ, ?_, ?_⟩
        · have hP : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Δ) := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  apply List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                  (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                      Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' ~
                      (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only
                    have eq2 : (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (z, E) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ++ Δ ~
              x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Δ) := by
              repeat rw [List.append_assoc]
              apply List.Perm.cons
              exact List.Perm.refl _
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hP)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ)] := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                  (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                      Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' ~
                      (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only
                    have eq2 : (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (z, E) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hzΔᵣ : z ∉ Δᵣ.names := by
              intro h
              have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; right ; left ; exact h
              exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
            have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
              have hp_z_block : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                have s1 : x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                    x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (z, E) :: Ξᵣ' := by
                  apply List.Perm.append (by rfl)
                  apply List.Perm.cons
                  apply List.Perm.cons
                  exact hPΞᵣ
                have s2 : x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (z, E) :: Ξᵣ' ~
                  x' ∶ A :: (z, E) :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  apply List.Perm.cons
                  have h1 : (z, E) :: (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
                    (Γᵣ ++ (z, E) :: y' ∶ C :: y ∶ D :: Ξᵣ') :=
                    List.perm_middle.symm
                  have h2 : (Γᵣ ++ (z, E) :: y' ∶ C :: y ∶ D :: Ξᵣ') ~
                    (Γᵣ ++ y' ∶ C :: (z, E) :: y ∶ D :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    exact List.Perm.swap ..
                  have h3 : (Γᵣ ++ y' ∶ C :: (z, E) :: y ∶ D :: Ξᵣ') ~
                    (Γᵣ ++ y' ∶ C  :: y ∶ D :: (z, E) :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    apply List.Perm.cons
                    exact List.Perm.swap ..
                  exact ((h1.trans h2).trans h3).symm
                exact s1.trans (s2.trans (List.Perm.swap ..))
              have hp_left : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] ~
                  (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x ∶ B :: Δᵣ] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
              have h_mid := HyperEnv.Perm.merge hp_left hp_z_block
              have h_rot : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x ∶ B :: Δᵣ] |ₕ
                  [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact (hPostL.trans h_mid).trans h_rot
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzx (by rfl)
                · exact hzΔᵣ (Env.mem_pair_fst_in_names _ hz_in)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzw (by rfl)
                · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
            have hnwin : w ∉ Env.names (z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
              intro h
              simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                Finset.mem_union] at h
              rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΓᵣΞᵣ
              · exact hwy.symm (by rfl)
              · exact hwy' (by rfl)
              · exact hwx' (by rfl)
              · exact hzw (by rfl)
              · have hΓ : w ∈ Γ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  rcases hΓᵣΞᵣ with hΓᵣ | hΞᵣ
                  · right ; right ; left ; exact hΓᵣ
                  · right ; right ; right ; right ; exact hΞᵣ
                exact hwΓ hΓ
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp only [List.mem_cons, Prod.mk.injEq] at hwin
                rcases hwin with ⟨rfl, _⟩ | hΔᵣ
                · exact hwx (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΔᵣ
                  exact hwΓ hΓ
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                exact hnwin (Env.mem_pair_fst_in_names _ hwin)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have h_LHS_perm : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
              𝒢' |ₕ [z ∶ E :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ [w ∶ Eᗮ :: Δ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              have h_rearrange : (x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ++ Δ ~
                x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ) := by
                rw [List.append_assoc]
                apply List.Perm.append (by rfl)
                rw [List.cons_append, List.cons_append]
              exact h_app.trans h_rearrange
            exact HyperEnv.Perm.merge h_cancel h_tail
          exact hP
      · refine ⟨𝒢, Γᵣ, Δᵣ, Ξᵣ' ++ Δ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Δ) := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' := by
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                  (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have h1 : (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' ~
                    Γᵣ ++ (z, E) :: Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append List.perm_middle.symm (by rfl)
                  have h2 : Γᵣ ++ (z, E) :: Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' ~
                    Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' := by
                    repeat rw [List.append_assoc]
                    apply List.Perm.append (by rfl)
                    exact List.perm_middle.symm
                  have h3 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' ~
                    Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) ::  Ξᵣ' := by
                    repeat rw [List.append_assoc]
                    apply List.Perm.append (by rfl)
                    apply List.Perm.append (by rfl)
                    apply List.Perm.swap ..
                  exact ((h1.trans h2).trans h3).symm
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ++ Δ ~
              x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Δ) := by
              rw [List.append_assoc]
              apply List.Perm.append (by rfl)
              rw [List.cons_append]
            exact (List.Perm.append hP1 (List.Perm.refl Δ)).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ)] := by
            have hP1 : Γ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                  (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (z, E) :: Ξᵣ' ~
                    Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' ~
                    (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (z, E) :: y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only
                    have eq2 : (z, E) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (z, E) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hzΓᵣ : z ∉ Γᵣ.names := by
              intro h
              have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; left ; exact h
              exact hzΓ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
            have h_subst : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                [w ∶ Eᗮ :: Δ] := by
              have hp_z_block : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                have s1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                  x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (z, E) :: Ξᵣ' := by
                  apply List.Perm.cons
                  apply List.Perm.append (by rfl)
                  apply List.Perm.cons
                  apply List.Perm.cons _ hPΞᵣ
                have s2 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (z, E) :: Ξᵣ' ~
                  x ∶ B :: (z, E) :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  apply List.Perm.cons
                  simp
                  have h1 : (z, E) :: (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
                    (Δᵣ ++ (z, E) :: y' ∶ C :: y ∶ D :: Ξᵣ') :=
                    List.perm_middle.symm
                  have h2 : (Δᵣ ++ (z, E) :: y' ∶ C :: y ∶ D :: Ξᵣ') ~
                    (Δᵣ ++ y' ∶ C :: (z, E) :: y ∶ D :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    exact List.Perm.swap ..
                  have h3 : (Δᵣ ++ y' ∶ C :: (z, E) :: y ∶ D :: Ξᵣ') ~
                    (Δᵣ ++ y' ∶ C :: y ∶ D :: (z, E) :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    apply List.Perm.cons
                    exact List.Perm.swap ..
                  exact ((h1.trans h2).trans h3).symm
                exact s1.trans (s2.trans (List.Perm.swap ..))
              have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                  (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x' ∶ A :: Γᵣ] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
              have h_mid := HyperEnv.Perm.merge hp_left hp_z_block
              have h_rot : (𝒢 |ₕ [w ∶ Eᗮ :: Δ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ
                  [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] ~
                (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                  [w ∶ Eᗮ :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact (hPostR.trans h_mid).trans h_rot
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzx' (by rfl)
                · exact hzΓᵣ (Env.mem_pair_fst_in_names _ hz_in)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzw (by rfl)
                · exact hzΔ (Env.mem_pair_fst_in_names _ hz_in)
            have hnwin : w ∉ Env.names (z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
              intro h
              simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                Finset.mem_union] at h
              rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΔᵣΞᵣ
              · exact hwy (by rfl)
              · exact hwy' (by rfl)
              · exact hwx (by rfl)
              · exact hzw (by rfl)
              · have hΓ : w ∈ Γ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  right ; right ; right ; exact hΔᵣΞᵣ
                exact hwΓ hΓ
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: Δ] := by
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp only [List.mem_cons, Prod.mk.injEq] at hwin
                rcases hwin with ⟨rfl, _⟩ | hΓᵣ
                · exact hwx' (by rfl)
                · have hΓ : w ∈ Γ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; left ; exact Env.mem_pair_fst_in_names _ hΓᵣ
                  exact hwΓ hΓ
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                exact hnwin (Env.mem_pair_fst_in_names _ hwin)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have h_LHS_perm : 𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] ~
              𝒢' |ₕ [z ∶ E :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ [w ∶ Eᗮ :: Δ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΓ') hPΔ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              have h_rearrange : (x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ++ Δ ~
                x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Δ) := by
                rw [List.append_assoc]
                rfl
              exact h_app.trans h_rearrange
            exact HyperEnv.Perm.merge h_cancel h_tail
          right ; exact hP
  · have hwin := (List.Perm.mem_iff (a := (w, Eᗮ)) hPE1).mp (by simp)
    simp only [List.cons_append, List.append_assoc, List.mem_cons,
      Prod.mk.injEq, List.mem_append] at hwin
    have hP𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [z ∶ E :: Γ] := by
      have h_subst := (HyperEnv.Perm.merge (by rfl : 𝒢 |ₕ [z ∶ E :: Γ] ~ _)
        (HyperEnv.Perm_singleton_singleton.mpr hPE1)).symm
      exact (HyperEnv.Perm_merge_cancel_right (h_subst.trans hP_pre)).symm
    rcases hwin with ⟨rfl, _⟩ | h1 | h2 | ⟨rfl, _⟩ | h3
    · exfalso ; exact hwx (by rfl)
    · obtain ⟨Γᵣ', hPΓᵣ⟩ := Env.exists_perm_cons h1
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ' ++ Γ, Δᵣ, Ξᵣ, ?_, ?_⟩
        · have hP : Γ ++ Δ ~ x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.cons
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have s1 : Γ ++ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                repeat rw [List.append_assoc]
                exact List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                simp
                apply List.perm_append_comm_assoc
              repeat rw [← List.append_assoc]
              exact s1.trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr hP)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: (Γᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append]
                simp only [← List.append_assoc, ← List.cons_append]
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hwΔᵣ : w ∉ Δᵣ.names := by
              intro h
              have hwin : w ∈ Env.names (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; right ; left ; exact h
              exact hwΔ ((Env.names_eq_of_perm hP1.symm) ▸ hwin)
            have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [z ∶ E :: Γ] := by
              have hp_w_block : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact (List.Perm.cons _ (List.Perm.append hPΓᵣ (List.Perm.refl _))).trans
                  (List.Perm.swap ..)
              have hp_left : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] ~
                (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x ∶ B :: Δᵣ] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
              have h_mid := hPostL.trans (HyperEnv.Perm.merge hp_left hp_w_block)
              have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x ∶ B :: Δᵣ] |ₕ
                  [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                  [z ∶ E :: Γ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact h_rot1.trans (h_mid.trans h_rot2)
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin
                rcases hzin with ⟨rfl, _⟩ | h
                · exact hzx (by rfl)
                · have := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr ?_
                  · exact hzΔ (Env.mem_pair_fst_in_names _ this)
                  · simp ; right ; right ; left ; exact h
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin
                rcases hzin with ⟨rfl, _⟩ | hzin
                · exact hzw (by rfl)
                · have hz_not : z ∉ Env.names (x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) := by
                    intro hz
                    simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union] at hz
                    rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                    · exact hzy (by rfl)
                    · exact hzy' (by rfl)
                    · exact hzx' (by rfl)
                    · have hΔ : z ∈ Δ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc,
                          Env.names_distributes, Env.names_merge, Finset.singleton_union,
                            Finset.union_insert, Finset.mem_insert, Finset.mem_union]
                        rcases h with hΓᵣ | hΞᵣ
                        · right ; right ; left ; exact hΓᵣ
                        · right ; right ; right ; right ; exact hΞᵣ
                      exact hzΔ hΔ
                  exfalso
                  apply hz_not
                  simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                    Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union]
                  rcases hzin with ⟨rfl, _⟩ | hΓᵣ' | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                  · right ; right ; left ; rfl
                  · right ; right ; right ; left
                    exact Env.mem_pair_fst_in_names _ hΓᵣ'
                  · right ; left ; rfl
                  · left ; rfl
                  · right ; right ; right ; right
                    exact Env.mem_pair_fst_in_names _ hΞᵣ
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~
              [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              have h_LHS : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin ; rcases hwin with ⟨rfl, _⟩ | hw_in
                · exact hwx (by rfl)
                · exact hwΔᵣ (Env.mem_pair_fst_in_names _ hw_in)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin ; rcases hwin with ⟨rfl, _⟩ | hw_in
                · exact hzw.symm (by rfl)
                · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
            have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [z ∶ E :: Γ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~
              [x' ∶ A :: (Γᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              simp at h_app
              have h_rearrange : Γ ++ x' ∶ A :: (Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                x' ∶ A :: (Γᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                have r1 : Γ ++ x' ∶ A :: (Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                  x' ∶ A :: Γ ++ (Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) := List.perm_middle
                have r2 : x' ∶ A :: Γ ++ (Γᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                  x' ∶ A :: (Γᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                  apply List.Perm.cons
                  simp
                  repeat rw [← List.append_assoc]
                  exact List.Perm.append (List.perm_append_comm) (by rfl)
                exact r1.trans r2
              exact h_app.trans h_rearrange
            exact HyperEnv.Perm.merge h_cancel h_tail
          exact hP
      · have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
          𝒢 |ₕ [x' ∶ A :: (Γᵣ' ++ Γ)] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
          have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
            have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
              x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              apply List.Perm.cons
              simp only [List.append_eq, List.append_assoc, List.cons_append]
              simp only [← List.append_assoc, ← List.cons_append]
              apply List.Perm.append ?_ (by rfl)
              apply List.Perm.append hPΓᵣ (by rfl)
            exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
          have hwΔᵣ : w ∉ Δᵣ.names := by
            intro h
            have hwin : w ∈ Env.names (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) := by
              simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
              right ; right ; right ; left ; exact h
            exact hwΔ ((Env.names_eq_of_perm hP1.symm) ▸ hwin)
          have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] |ₕ
                [z ∶ E :: Γ] := by
            have hp_w_block : [x' ∶ A :: Γᵣ] ~ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact (List.Perm.cons _ hPΓᵣ).trans (List.Perm.swap ..)
            have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] :=
              (HyperEnv.Perm.merge hP𝒢ᵣ hp_w_block)
            have h_mid := hPostR.trans
              (HyperEnv.Perm.merge hp_left
                (by rfl : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~ _))
            have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] |ₕ
                [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
                [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] |ₕ [z ∶ E :: Γ] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_rot1.trans (h_mid.trans h_rot2)
          have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
            have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                (Env.mem_pair_fst_in_names _ hzE2))
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin ; rcases hzin with ⟨rfl, _⟩ | hz_in
              · exact hzx (by rfl)
              · have hz_not : z ∉ (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                  intro hz
                  simp only [Env.names_merge, Env.names_distributes,
                    Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union] at hz
                  rcases hz with rfl | rfl | hΔᵣ | hΞᵣ
                  · exact hzy (by rfl)
                  · exact hzy' (by rfl)
                  · have hΔ : z ∈ Δ.names := by
                      rw [Env.names_eq_of_perm hP1]
                      simp only [List.cons_append, List.append_assoc,
                        Env.names_distributes, Env.names_merge,
                        Finset.singleton_union, Finset.union_insert,
                        Finset.mem_insert, Finset.mem_union]
                      right ; right ; right ; left ; exact hΔᵣ
                    exact hzΔ hΔ
                  · have hΔ : z ∈ Δ.names := by
                      rw [Env.names_eq_of_perm hP1]
                      simp only [List.cons_append, List.append_assoc,
                        Env.names_distributes, Env.names_merge, Finset.singleton_union,
                        Finset.union_insert, Finset.mem_insert, Finset.mem_union]
                      right ; right ; right ; right ; exact hΞᵣ
                    exact hzΔ hΔ
                rcases hz_in with hΔᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                · apply hz_not
                  simp only [Env.names_merge, Env.names_distributes,
                    Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union]
                  right ; right ; left ; exact (Env.mem_pair_fst_in_names _ hΔᵣ)
                · exact hzy' (by rfl)
                · exact hzy (by rfl)
                · apply hz_not
                  simp only [Env.names_merge, Env.names_distributes,
                    Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union]
                  right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin
              rcases hzin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΓᵣ
              · exact hzw (by rfl)
              · exact hzx' (by rfl)
              · exfalso
                have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [hΓᵣ])
                exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] := by
            have h_LHS : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                (Env.mem_pair_fst_in_names _ hwE2))
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin
              rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hwx (by rfl)
              · have hw_not : w ∉ (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                  intro hw
                  simp only [Env.names_merge, Env.names_distributes,
                    Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union] at hw
                  rcases hw with rfl | rfl | hΔᵣ | hΞᵣ
                  · exact hwy (by rfl)
                  · exact hwy' (by rfl)
                  · exact hwΔᵣ hΔᵣ
                  · have hΔ : w ∈ Δ.names := by
                      rw [Env.names_eq_of_perm hP1]
                      simp only [List.cons_append, List.append_assoc,
                        Env.names_distributes, Env.names_merge, Finset.singleton_union,
                        Finset.union_insert, Finset.mem_insert, Finset.mem_union]
                      right ; right ; right ; right ; exact hΞᵣ
                    exact hwΔ hΔ
                rcases hw_in with hΔᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                · exact hwΔᵣ (Env.mem_pair_fst_in_names _ hΔᵣ)
                · exact hwy' (by rfl)
                · exact hwy (by rfl)
                · apply hw_not
                  simp only [Env.names_merge, Env.names_distributes,
                    Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                    Finset.mem_union]
                  right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin
              rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hzw.symm (by rfl)
              · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
          have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ'] |ₕ [z ∶ E :: Γ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
          have h_cancel := h_LHS_perm.symm.trans h_subst
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          have h_tail : [Γ'‚ Δ'] ~ [x' ∶ A :: (Γᵣ' ++ Γ)] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
            have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
            have h_app := List.Perm.append hp1 hp2
            have h_rearrange : Γ ++ x' ∶ A :: Γᵣ' ~ x' ∶ A :: (Γᵣ' ++ Γ) := by
              have r1 : Γ ++ x' ∶ A :: Γᵣ' ~ x' ∶ A :: Γ ++ Γᵣ' := List.perm_middle
              have r2 : x' ∶ A :: Γ ++ Γᵣ' ~ x' ∶ A :: (Γᵣ' ++ Γ) := by
                apply List.Perm.cons
                exact List.perm_append_comm
              exact r1.trans r2
            exact h_app.trans h_rearrange
          have h_merged := HyperEnv.Perm.merge h_cancel h_tail
          have h_rot_final : (𝒢 |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
              [x' ∶ A :: (Γᵣ' ++ Γ)] ~
            𝒢 |ₕ [x' ∶ A :: (Γᵣ' ++ Γ)] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm_merge_cancel_right_inv
            exact HyperEnv.Perm.merge_comm
          exact h_merged.trans h_rot_final
        refine ⟨𝒢, Γᵣ' ++ Γ, Δᵣ, Ξᵣ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append]
                simp only [← List.append_assoc, ← List.cons_append]
                apply List.Perm.append ?_ (by rfl)
                apply List.Perm.append hPΓᵣ (by rfl)
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
              have s1 :Γ ++ (x ∶ A ⨂ B :: Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) :=
                List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ' ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: (Γᵣ' ++ Γ) ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                simp
                apply List.perm_append_comm_assoc
              exact s1.trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · right ; exact hP
    · obtain ⟨Δᵣ', hPΔᵣ⟩ := Env.exists_perm_cons h2
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ, Δᵣ' ++ Γ, Ξᵣ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
              x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
              have s1 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have r1 : Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                  Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                  have eq1 : Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) =
                    (Γ ++ Γᵣ) ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                    repeat rw [← List.append_assoc]
                  have eq2 : Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) =
                    (Γᵣ ++ Γ) ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by rw [← List.append_assoc]
                  rw [eq1, eq2]
                  exact List.Perm.append List.perm_append_comm (List.Perm.refl _)
                have r2 : Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                  Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                  rw [List.append_assoc, List.append_assoc]
                  apply List.Perm.append (by rfl)
                  have eq3 : Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) =
                    (Γ ++ Δᵣ') ++ y ∶ C ⅋ D :: Ξᵣ := by rw [← List.append_assoc]
                  rw [eq3]
                  exact List.Perm.append List.perm_append_comm (List.Perm.refl _)
                exact r1.trans r2
              exact s1.trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl)
            (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: Δᵣ' ++ Γ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                    Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hzΓᵣ : z ∉ Γᵣ.names := by
              intro h
              have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
                right ; right ; left ; exact h
              exact hzΔ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
            have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] |ₕ
                  [z ∶ E :: Γ] := by
              have hp_w_block : [x ∶ B :: Δᵣ] ~ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact (List.Perm.cons _ hPΔᵣ).trans (List.Perm.swap ..)
              have hp_left : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] ~
                  (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ hp_w_block)
              have h_mid := hPostL.trans
                (HyperEnv.Perm.merge hp_left
                  (by rfl : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~ _))
              have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] |ₕ
                  [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
                  [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] |ₕ [z ∶ E :: Γ] := by
                apply HyperEnv.Perm_rotate_rhs_left
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm_rotate_rhs_left
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact h_rot1.trans (h_mid.trans h_rot2)
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin
                rcases hzin with ⟨rfl, _⟩ | hz_in
                · exact hzx' (by rfl)
                · have hz_not : z ∉ (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                    intro hz
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union] at hz
                    rcases hz with rfl | rfl | hΓᵣ | hΞᵣ
                    · exact hzy (by rfl)
                    · exact hzy' (by rfl)
                    · exact hzΓᵣ hΓᵣ
                    · have hΔ : z ∈ Δ.names := by
                        rw[Env.names_eq_of_perm hP1]
                        simp [hΞᵣ]
                      exact hzΔ hΔ
                  rcases hz_in with hΓᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                  · exact hzΓᵣ (Env.mem_pair_fst_in_names _ hΓᵣ)
                  · exact hzy' (by rfl)
                  · exact hzy (by rfl)
                  · apply hz_not
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union]
                    right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin
                rcases hzin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h
                · exact hzw (by rfl)
                · exact hzx (by rfl)
                · have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [h])
                  exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] := by
              have h_LHS : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin
                rcases hwin with ⟨rfl, _⟩ | hw_in
                · exact hwx' (by rfl)
                · have hw_not : w ∉ (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ).names := by
                    intro hw
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union] at hw
                    rcases hw with rfl | rfl | hΓᵣ | hΞᵣ
                    · exact hwy (by rfl)
                    · exact hwy' (by rfl)
                    · have hw_in_Δ : w ∈ Δ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc,
                          Env.names_distributes, Env.names_merge,
                          Finset.singleton_union, Finset.union_insert,
                          Finset.mem_insert, Finset.mem_union]
                        right ; right ; left ; exact hΓᵣ
                      exact hwΔ hw_in_Δ
                    · have hw_in_Δ : w ∈ Δ.names := by
                        rw [Env.names_eq_of_perm hP1]
                        simp only [List.cons_append, List.append_assoc,
                          Env.names_distributes, Env.names_merge,
                          Finset.singleton_union, Finset.union_insert,
                          Finset.mem_insert, Finset.mem_union]
                        right ; right ; right ; right ; exact hΞᵣ
                      exact hwΔ hw_in_Δ
                  rcases hw_in with hΓᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
                  · apply hw_not
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union]
                    right ; right ; left ; exact (Env.mem_pair_fst_in_names _ hΓᵣ)
                  · exact hwy' (by rfl)
                  · exact hwy (by rfl)
                  · apply hw_not
                    simp only [Env.names_merge, Env.names_distributes,
                      Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                      Finset.mem_union]
                    right ; right ; right ; exact (Env.mem_pair_fst_in_names _ hΞᵣ)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin
                rcases hwin with ⟨rfl, _⟩ | hw_in
                · exact hzw.symm (by rfl)
                · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
            have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ'] |ₕ [z ∶ E :: Γ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: (Δᵣ' ++ Γ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              have h_rearrange : Γ ++ x ∶ B :: Δᵣ' ~ x ∶ B :: (Δᵣ' ++ Γ) := by
                have r1 : Γ ++ x ∶ B :: Δᵣ' ~ x ∶ B :: Γ ++ Δᵣ' := List.perm_middle
                have r2 : x ∶ B :: Γ ++ Δᵣ' ~ x ∶ B :: (Δᵣ' ++ Γ) := by
                  apply List.Perm.cons
                  exact List.perm_append_comm
                exact r1.trans r2
              exact h_app.trans h_rearrange
            have h_merged := HyperEnv.Perm.merge h_cancel h_tail
            have h_rot_final : (𝒢 |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) |ₕ
                [x ∶ B :: Δᵣ' ++ Γ] ~
              𝒢 |ₕ [x ∶ B :: Δᵣ' ++ Γ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_merged.trans h_rot_final
          exact hP
      · have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
          𝒢 |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: (Δᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
          have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
            have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
              x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              apply List.Perm.cons
              have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                repeat rw [List.append_assoc]
                apply List.Perm.append (by rfl)
                apply List.Perm.append hPΔᵣ (by rfl)
              have s2 : Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                  (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                exact List.Perm.append List.perm_middle (List.Perm.refl _)
              exact s1.trans s2
            exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
          have hzΓᵣ : z ∉ Γᵣ.names := by
            intro h
            have hzin : z ∈ Env.names (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
              simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
              right ; right ; left ; exact h
            exact hzΔ ((Env.names_eq_of_perm hP1.symm) ▸ hzin)
          have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [z ∶ E :: Γ] := by
            have hp_w_block : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have s1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                  x ∶ B :: (w, Eᗮ) :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                apply List.Perm.cons
                exact List.Perm.append hPΔᵣ (List.Perm.refl _)
              exact s1.trans (List.Perm.swap ..)
            have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x' ∶ A :: Γᵣ] :=
              (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
            have h_mid := hPostR.trans (HyperEnv.Perm.merge hp_left hp_w_block)
            have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ
                [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ
                [z ∶ E :: Γ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_rot1.trans (h_mid.trans h_rot2)
          have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
            have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                (Env.mem_pair_fst_in_names _ hzE2))
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin
              rcases hzin with ⟨rfl, _⟩ | hz_in
              · exact hzx' (by rfl)
              · exact hzΓᵣ (Env.mem_pair_fst_in_names _ hz_in)
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin
              rcases hzin with ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΔᵣ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΞᵣ
              · exact hzw (by rfl)
              · exact hzx (by rfl)
              · have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [hΔᵣ])
                exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
              · exact hzy' (by rfl)
              · exact hzy (by rfl)
              · have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [hΞᵣ])
                exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          have hPΔ' : [w ∶ Eᗮ :: Δ'] ~
            [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            have h_LHS : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                (Env.mem_pair_fst_in_names _ hwE2))
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin
              rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hwx' (by rfl)
              · have hw_not : w ∉ Γᵣ.names := by
                  intro hw
                  have hΔ : w ∈ Δ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; left ; exact hw
                  exact hwΔ hΔ
                exact hw_not (Env.mem_pair_fst_in_names _ hw_in)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin
              rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hzw.symm (by rfl)
              · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
          have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ] |ₕ [z ∶ E :: Γ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
          have h_cancel := h_LHS_perm.symm.trans h_subst
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: (Δᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
            have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
            have h_app := List.Perm.append hp1 hp2
            simp at h_app
            have h_rearrange : Γ ++ x ∶ B :: (Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
              x ∶ B :: (Δᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
              have r1 : Γ ++ x ∶ B :: (Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                  x ∶ B :: Γ ++ (Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) := List.perm_middle
              have r2 : x ∶ B :: Γ ++ (Δᵣ' ++ y' ∶ C :: y ∶ D :: Ξᵣ) ~
                  x ∶ B :: (Δᵣ' ++ Γ) ++ y' ∶ C :: y ∶ D :: Ξᵣ := by
                apply List.Perm.cons
                simp
                rw [← List.append_assoc]
                conv_rhs => rw [← List.append_assoc]
                apply List.Perm.append ?_ (by rfl)
                exact List.perm_append_comm
              exact r1.trans r2
            exact h_app.trans h_rearrange
          exact HyperEnv.Perm.merge h_cancel h_tail
        refine ⟨𝒢, Γᵣ, Δᵣ' ++ Γ, Ξᵣ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append hPΔᵣ (by rfl)
                have s2 : Γᵣ ++ (w, Eᗮ) :: Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ ~
                  (w, Eᗮ) :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ := by
                  exact List.Perm.append List.perm_middle (List.Perm.refl _)
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
              have s1 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                x ∶ A ⨂ B :: Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                apply List.Perm.cons
                have r1 : Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                  Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                  have eq1 : Γ ++ (Γᵣ ++ Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) =
                    (Γ ++ Γᵣ) ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by
                    repeat rw [← List.append_assoc]
                  have eq2 : Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) =
                    (Γᵣ ++ Γ) ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) := by rw [← List.append_assoc]
                  rw [eq1, eq2]
                  exact List.Perm.append List.perm_append_comm (List.Perm.refl _)
                have r2 : Γᵣ ++ Γ ++ (Δᵣ' ++ y ∶ C ⅋ D :: Ξᵣ) ~
                  Γᵣ ++ (Δᵣ' ++ Γ) ++ y ∶ C ⅋ D :: Ξᵣ := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  rw [← List.append_assoc]
                  conv_rhs => rw [← List.append_assoc]
                  exact List.Perm.append List.perm_append_comm (by rfl)
                exact r1.trans r2
              exact s1.trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · right ; exact hP
    · exfalso ; exact hwy (by rfl)
    · obtain ⟨Ξᵣ', hPΞᵣ⟩ := Env.exists_perm_cons h3
      rcases hP_post with hPostL | hPostR
      · refine ⟨𝒢, Γᵣ, Δᵣ, Ξᵣ' ++ Γ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                    Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                      Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' ~
                      (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' := by simp only
                    have eq2 : (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (w, Eᗮ) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
              x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
              have s1 : Γ ++ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') := by
                repeat rw [List.append_assoc]
                apply List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
                apply List.Perm.cons
                have r1 : Γ ++ (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                  (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ++ Γ := List.perm_append_comm
                have eq1 : (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ++ Γ =
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
                  repeat rw [List.append_assoc]
                  apply congrArg
                  apply congrArg
                  rw [← List.cons_append]
                rw [eq1] at r1
                exact r1
              have s3 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                Γ ++ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                simp only [List.append_assoc, List.cons_append, Env.Perm.refl]
              exact (s3.trans s1).trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · left
          have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
            𝒢 |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ)] := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                    Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                      Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' ~
                      (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' := by simp only
                    have eq2 : (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (w, Eᗮ) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
            have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                  [z ∶ E :: Γ] := by
              have hp_w_block : [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                  [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                have s1 : x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                    x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' := by
                  apply List.Perm.cons
                  apply List.Perm.append (by rfl)
                  apply List.Perm.cons
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' ~
                    (w, Eᗮ) :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  have p1 : x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' ~
                      x' ∶ A :: Γᵣ ++ y' ∶ C :: (w, Eᗮ) :: y ∶ D :: Ξᵣ' := by
                    apply List.Perm.cons
                    apply List.Perm.append (by rfl)
                    apply List.Perm.cons
                    exact List.Perm.swap ..
                  have p2 : x' ∶ A :: Γᵣ ++ y' ∶ C :: (w, Eᗮ) :: y ∶ D :: Ξᵣ' ~
                      x' ∶ A :: Γᵣ ++ (w, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ' := by
                    apply List.Perm.cons
                    apply List.Perm.append (by rfl)
                    exact List.Perm.swap ..
                  have p3 : x' ∶ A :: Γᵣ ++ (w, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ' ~
                      x' ∶ A :: (w, Eᗮ) :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                    apply List.Perm.cons
                    simp only [List.append_eq, List.cons_append, List.perm_middle]
                  exact ((p1.trans p2).trans p3).trans (List.Perm.swap ..)
                exact s1.trans s2
              have hp_left : 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] ~
                  (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x ∶ B :: Δᵣ] :=
                (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
              have h_mid := hPostL.trans (HyperEnv.Perm.merge hp_left hp_w_block)
              have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x ∶ B :: Δᵣ] |ₕ
                  [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] ~
                (𝒢 |ₕ [x ∶ B :: Δᵣ]) |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                  [z ∶ E :: Γ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                rw [← HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_cancel_right_inv
                exact HyperEnv.Perm.merge_comm
              exact h_rot1.trans (h_mid.trans h_rot2)
            have hznin : z ∉
              Env.names (w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
              intro h
              simp only [List.cons_append, Env.names_distributes, Env.names_merge,
                Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
                Finset.mem_union] at h
              rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΓᵣΞᵣ
              · exact hzy (by rfl)
              · exact hzy' (by rfl)
              · exact hzx' (by rfl)
              · exact hzw (by rfl)
              · have hΔ : z ∈ Δ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  rcases hΓᵣΞᵣ with hΓᵣ | hΞᵣ
                  · right ; right ; left ; exact hΓᵣ
                  · right ; right ; right ; right  ; exact hΞᵣ
                exact hzΔ hΔ
            have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
              have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hzE2))
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                simp at hzin ; rcases hzin with ⟨rfl, _⟩ | h
                · exact hzx (by rfl)
                · have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [h])
                  exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
              · exfalso
                have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
                exact hznin (Env.mem_pair_fst_in_names _ hzin)
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            have hPΔ' : [w ∶ Eᗮ :: Δ'] ~
              [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
              have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
              obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
              simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
              rcases hE2 with h𝒢 | rfl | rfl | rfl
              · exfalso
                have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
                exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢
                  (Env.mem_pair_fst_in_names _ hwE2))
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin
                rcases hwin with ⟨rfl, _⟩ | h
                · exact hwx (by rfl)
                · have hΔ : w ∈ Δ.names := by
                    rw [Env.names_eq_of_perm hP1]
                    simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                      Env.names_merge, Finset.singleton_union, Finset.union_insert,
                      Finset.mem_insert, Finset.mem_union]
                    right ; right ; right ; left ; exact Env.mem_pair_fst_in_names _ h
                  exact hwΔ hΔ
              · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
              · exfalso
                have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
                simp at hwin ; rcases hwin with ⟨rfl, _⟩ | hw_in
                · exact hzw.symm (by rfl)
                · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
            have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
                𝒢' |ₕ [w ∶ Eᗮ :: x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ [z ∶ E :: Γ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
            have h_cancel := h_LHS_perm.symm.trans h_subst
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            apply HyperEnv.Perm_merge_cancel_right at h_cancel
            have hP_tail : [Γ'‚ Δ'] ~ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ)] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
              have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
              have h_app := List.Perm.append hp1 hp2
              simp only [List.append_eq, List.cons_append] at h_app
              have h_rearrange : Γ ++ x' ∶ A :: (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
                x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ) := by
                have r1 : Γ ++ x' ∶ A :: (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
                  x' ∶ A :: Γ ++ Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  exact List.perm_middle
                have r2 : x' ∶ A :: Γ ++ Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' ~
                  x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ) := by
                  apply List.Perm.cons
                  simp
                  have h1 : Γᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ) ~
                    Γᵣ ++ y' ∶ C :: y ∶ D :: (Γ ++ Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    apply List.Perm.cons
                    apply List.Perm.cons
                    exact List.perm_append_comm
                  have h2 : Γᵣ ++ y' ∶ C :: y ∶ D :: (Γ ++ Ξᵣ') ~
                    Γᵣ ++ (y' ∶ C :: Γ ++ y ∶ D :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    apply List.Perm.cons
                    exact List.perm_middle.symm
                  have h3 : Γᵣ ++ (y' ∶ C :: Γ ++ y ∶ D :: Ξᵣ') ~
                    Γᵣ ++ (Γ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
                    apply List.Perm.append (by rfl)
                    exact List.perm_middle.symm
                  have h4 : Γᵣ ++ (Γ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
                    Γ ++ (Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
                    rw [← List.append_assoc]
                    conv_rhs => rw [← List.append_assoc]
                    exact List.Perm.append (List.perm_append_comm) (by rfl)
                  exact (((h1.trans h2).trans h3).trans h4).symm
                exact r1.trans r2
              apply h_app.trans h_rearrange
            exact HyperEnv.Perm.merge h_cancel hP_tail
          exact hP
      · have hP : 𝒢' |ₕ [Γ'‚ Δ'] ~
          𝒢 |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ)] := by
          have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
            have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
              x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              apply List.Perm.cons
              have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                  Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' := by
                repeat rw [List.append_assoc]
                apply List.Perm.append (by rfl)
                apply List.Perm.append (by rfl)
                exact List.Perm.cons _ hPΞᵣ
              have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                  (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                    Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' :=
                  List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                have p2 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have eq1 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' =
                    (Γᵣ ++ Δᵣ) ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' := by simp only
                  have eq2 : (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                    (w, Eᗮ) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    simp only [List.cons_append, List.append_assoc]
                  rw [eq1, eq2]
                  exact List.perm_middle
                exact p1.trans p2
              exact s1.trans s2
            exact List.Perm.cons_inv (hPE1.trans (this.trans (List.Perm.swap ..)))
          have hzΓᵣ : z ∶ E ∉ Γᵣ := by
            intro h
            have hΔ := (List.Perm.mem_iff (a := z ∶ E) hP1).mpr (by simp [h])
            exact hzΔ (Env.mem_pair_fst_in_names _ hΔ)
          have h_subst : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                [z ∶ E :: Γ] := by
            have hp_w_block : [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ] ~
                [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              have s1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ ~
                  x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' := by
                apply List.Perm.cons
                apply List.Perm.append (by rfl)
                apply List.Perm.cons
                exact List.Perm.cons _ hPΞᵣ
              have s2 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' ~
                (w, Eᗮ) :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                have p1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (w, Eᗮ) :: Ξᵣ' ~
                  x ∶ B :: Δᵣ ++ y' ∶ C :: (w, Eᗮ) :: y ∶ D :: Ξᵣ' := by
                  apply List.Perm.cons
                  apply List.Perm.append (by rfl)
                  apply List.Perm.cons
                  exact List.Perm.swap ..
                have p2 : x ∶ B :: Δᵣ ++ y' ∶ C :: (w, Eᗮ) :: y ∶ D :: Ξᵣ' ~
                  x ∶ B :: Δᵣ ++ (w, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  apply List.Perm.cons
                  apply List.Perm.append (by rfl)
                  exact List.Perm.swap ..
                have p3 : x ∶ B :: Δᵣ ++ (w, Eᗮ) :: y' ∶ C :: y ∶ D :: Ξᵣ' ~
                  x ∶ B :: (w, Eᗮ) :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                  apply List.Perm.cons
                  simp
                exact ((p1.trans p2).trans p3).trans (List.Perm.swap ..)
              exact s1.trans s2
            have hp_left : 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] ~
                (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x' ∶ A :: Γᵣ] :=
              (HyperEnv.Perm.merge hP𝒢ᵣ (by rfl))
            have h_mid := hPostR.trans (HyperEnv.Perm.merge hp_left hp_w_block)
            have h_rot1 : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [z ∶ E :: Γ'] |ₕ [w ∶ Eᗮ :: Δ'] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            have h_rot2 : (𝒢 |ₕ [z ∶ E :: Γ]) |ₕ [x' ∶ A :: Γᵣ] |ₕ
                [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] ~
              (𝒢 |ₕ [x' ∶ A :: Γᵣ]) |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ
                [z ∶ E :: Γ] := by
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm_merge_cancel_right_inv
              rw [← HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_cancel_right_inv
              exact HyperEnv.Perm.merge_comm
            exact h_rot1.trans (h_mid.trans h_rot2)
          have hznin : z ∉ Env.names (w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by
            intro h
            simp only [List.cons_append, Env.names_distributes, Env.names_merge,
              Finset.singleton_union, Finset.union_insert, Finset.mem_insert,
              Finset.mem_union] at h
            rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | hΔᵣΞᵣ
            · exact hzy (by rfl)
            · exact hzy' (by rfl)
            · exact hzx (by rfl)
            · exact hzw (by rfl)
            · have hΔ : z ∈ Δ.names := by
                rw [Env.names_eq_of_perm hP1]
                simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                  Env.names_merge, Finset.singleton_union, Finset.union_insert,
                  Finset.mem_insert, Finset.mem_union]
                right ; right ; right ; exact hΔᵣΞᵣ
              exact hzΔ hΔ
          have hPΓ' : [z ∶ E :: Γ'] ~ [z ∶ E :: Γ] := by
            have hin : (z ∶ E :: Γ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hzE2 : (z, E) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hz𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hzE2))
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              simp at hzin
              rcases hzin with ⟨rfl, _⟩ | h
              · exact hzx' (by rfl)
              · exact hzΓᵣ h
            · exfalso
              have hzin := (List.Perm.mem_iff (a := z ∶ E) hPE2).mpr (by simp)
              exact hznin (Env.mem_pair_fst_in_names _ hzin)
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
          have hPΔ' : [w ∶ Eᗮ :: Δ'] ~ [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] := by
            have hin : (w ∶ Eᗮ :: Δ') ∈ 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] := by simp
            obtain ⟨E2, hE2, hPE2⟩ := HyperEnv.Perm_mem h_subst.symm hin
            simp only [List.mem_append, List.mem_singleton, or_assoc] at hE2
            rcases hE2 with h𝒢 | rfl | rfl | rfl
            · exfalso
              have hwE2 : (w, Eᗮ) ∈ E2 := (List.Perm.mem_iff hPE2).mpr (by simp)
              exact hw𝒢 (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hwE2))
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin ; rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hwx' (by rfl)
              · have hw_in_Δ : w ∈ Δ.names := by
                  rw [Env.names_eq_of_perm hP1]
                  simp only [List.cons_append, List.append_assoc, Env.names_distributes,
                    Env.names_merge, Finset.singleton_union, Finset.union_insert,
                    Finset.mem_insert, Finset.mem_union]
                  right ; right ; left ; exact Env.mem_pair_fst_in_names _ hw_in
                exact hwΔ hw_in_Δ
            · exact HyperEnv.Perm_singleton_singleton.mpr hPE2.symm
            · exfalso
              have hwin := (List.Perm.mem_iff (a := w ∶ Eᗮ) hPE2).mpr (by simp)
              simp at hwin ; rcases hwin with ⟨rfl, _⟩ | hw_in
              · exact hzw.symm (by rfl)
              · exact hwΓ (Env.mem_pair_fst_in_names _ hw_in)
          have h_LHS_perm : 𝒢' |ₕ [w ∶ Eᗮ :: Δ'] |ₕ [z ∶ E :: Γ'] ~
              𝒢' |ₕ [w ∶ Eᗮ :: x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ'] |ₕ [z ∶ E :: Γ] :=
            HyperEnv.Perm.merge (HyperEnv.Perm.merge (by rfl) hPΔ') hPΓ'
          have h_cancel := h_LHS_perm.symm.trans h_subst
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          apply HyperEnv.Perm_merge_cancel_right at h_cancel
          have h_tail : [Γ'‚ Δ'] ~ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ)] := by
            rw [HyperEnv.Perm_singleton_singleton]
            have hp1 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΓ')
            have hp2 := List.Perm.cons_inv (HyperEnv.Perm_singleton_singleton.mp hPΔ')
            have h_app := List.Perm.append hp1 hp2
            simp at h_app
            have h_rearrange : (Γ ++ x ∶ B :: (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') ~
              x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ)) := by
              have h1 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Ξᵣ' ++ Γ) ~
                x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Γ ++ Ξᵣ') := by
                apply List.Perm.cons
                apply List.Perm.append (by rfl)
                apply List.Perm.cons
                apply List.Perm.cons
                exact List.perm_append_comm
              have h2 : x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: (Γ ++ Ξᵣ') ~
                x ∶ B :: Δᵣ ++ y' ∶ C :: Γ ++ y ∶ D :: Ξᵣ' := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append]
                apply List.Perm.append (by rfl)
                apply List.Perm.cons
                exact List.perm_middle.symm
              have h3 : x ∶ B :: Δᵣ ++ y' ∶ C :: Γ ++ y ∶ D :: Ξᵣ' ~
                x ∶ B :: Δᵣ ++ Γ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                apply List.Perm.cons
                simp only [List.append_eq, List.append_assoc, List.cons_append]
                apply List.Perm.append (by rfl)
                exact List.perm_middle.symm
              have h4 : x ∶ B :: Δᵣ ++ Γ ++ y' ∶ C :: y ∶ D :: Ξᵣ' ~
                Γ ++ x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' := by
                apply List.Perm.append
                · apply (List.Perm.cons _ List.perm_append_comm).trans
                    List.perm_middle.symm
                · rfl
              have h5 : Γ ++ x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ' ~
                Γ ++ x ∶ B :: (Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ') := by simp
              exact ((((h1.trans h2).trans h3).trans h4).trans h5).symm
            apply h_app.trans h_rearrange
          exact HyperEnv.Perm.merge h_cancel h_tail
        refine ⟨𝒢, Γᵣ, Δᵣ, Ξᵣ' ++ Γ, ?_, ?_⟩
        · have h_pre : Γ ++ Δ ~
            x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
            have hP1 : Δ ~ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
              have : x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                x ∶ A ⨂ B :: (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                apply List.Perm.cons
                have s1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ ~
                    Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' := by
                  repeat rw [List.append_assoc]
                  apply List.Perm.append (by rfl)
                  apply List.Perm.append (by rfl)
                  exact List.Perm.cons _ hPΞᵣ
                have s2 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                    (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  have p1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (w, Eᗮ) :: Ξᵣ' ~
                      Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' :=
                    List.Perm.append (List.Perm.refl _) (List.Perm.swap ..)
                  have p2 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' ~
                      (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                    have eq1 : Γᵣ ++ Δᵣ ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' =
                      (Γᵣ ++ Δᵣ) ++ (w, Eᗮ) :: y ∶ C ⅋ D :: Ξᵣ' := by simp only
                    have eq2 : (w, Eᗮ) :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' =
                      (w, Eᗮ) :: (Γᵣ ++ Δᵣ) ++ y ∶ C ⅋ D :: Ξᵣ' := by
                      simp only [List.cons_append, List.append_assoc]
                    rw [eq1, eq2]
                    exact List.perm_middle
                  exact p1.trans p2
                exact s1.trans s2
              exact List.Perm.cons_inv (hPE1.trans
                (this.trans (List.Perm.swap ..)))
            have hP2 : Γ ++ (x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
              have s1 : Γ ++ x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' ~
                x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') :=  by
                repeat rw [List.append_assoc]
                apply List.perm_middle
              have s2 : x ∶ A ⨂ B :: Γ ++ (Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                x ∶ A ⨂ B :: Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) := by
                apply List.Perm.cons
                simp
                rw [← List.append_assoc, ← List.append_assoc]
                conv_rhs => rw [← List.append_assoc]
                have h1 : Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: (Ξᵣ' ++ Γ) ~
                  Γᵣ ++ Δᵣ ++ (Γ ++ y ∶ C ⅋ D :: Ξᵣ') := by
                  apply List.Perm.append (by rfl)
                  apply (List.Perm.cons _ List.perm_append_comm).trans
                    List.perm_middle.symm
                have h2 : Γᵣ ++ Δᵣ ++ (Γ ++ y ∶ C ⅋ D :: Ξᵣ') ~
                  Γ ++ Γᵣ ++ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ' := by
                  rw [← List.append_assoc]
                  apply List.Perm.append ?_ (by rfl)
                  rw [List.append_assoc, List.append_assoc]
                  exact (List.Perm.append_left _
                    List.perm_append_comm).trans
                    (List.perm_append_comm_assoc _ _ _).symm
                exact (h1.trans h2).symm
              rw [← List.append_assoc, ← List.append_assoc]
              apply s1.trans s2
            exact (List.Perm.append (List.Perm.refl Γ) hP1).trans hP2
          exact HyperEnv.Perm.merge (by rfl) (HyperEnv.Perm_singleton_singleton.mpr h_pre)
        · right ; exact hP
