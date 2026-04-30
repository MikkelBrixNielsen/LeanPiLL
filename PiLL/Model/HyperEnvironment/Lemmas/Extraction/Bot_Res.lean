import PiLL.Model.HyperEnvironment.Lemmas.Basic

lemma HyperEnv.Perm.extract_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (hzx : z ≠ x) (hzy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hFx' : x ∉ ℋ.names) (hFy' : y ∉ ℋ.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by
  have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · rcases h with hE𝒢 | hEΓx
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ξz : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Ξ, ?_, ?_⟩
      · apply HyperEnv.Perm.trans
        · exact HyperEnv.Perm.merge_right h𝒢Ξz [Γ‚ Δ]
        · have := (HyperEnv.Perm_merge_singleton (z ∶ ⊥ :: Ξ) (𝒢ᵣ' |ₕ [Γ‚ Δ])).symm
          rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
          exact this
      · have h_pre_subst : 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] ~
          ([z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ') |ₕ ([x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ξz h_pre
          exact this.symm
        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post
        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst
        have hEy : y ∶ Aᗮ :: Δ' ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
        obtain ⟨Ey, hEy', hPEy⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hEy
        have hyA: (y ∶ Aᗮ) ∈ Ey := by
            simp [HasPerm.perm] at hPEy
            have := hPEy.symm.subset
            simp only [List.cons_subset] at this
            exact this.1
        have hyinEy : y ∈ Ey.names := by
          exact Env.mem_pair_fst_in_names _ hyA
        simp only [List.mem_append, List.mem_singleton] at hEy'
        rcases hEy' with h1 | rfl | rfl | rfl
        · cases h1 with
          | inl h1' =>
            cases h1' with
            | inl hin𝒢ᵣ =>
              exfalso
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem hin𝒢ᵣ) hyinEy]
            | inr hEyΞ =>
              exfalso
              symm at hEyΞ
              subst hEyΞ
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
              apply Or.inl
              use Aᗮ
              apply (List.Perm.mem_iff (a := (y ∶ Aᗮ)) hPE).mpr
              simp only [List.mem_cons, Prod.mk.injEq]
              exact Or.inr hyA
          | inr hEyΓx =>
            exfalso
            symm at hEyΓx
            subst hEyΓx
            simp only [List.mem_cons] at hyA
            rcases hyA with heq | hyinΓ
            · injection heq with heq_name _
              exact hneq heq_name.symm
            · exact hyΓ (Env.mem_pair_fst_in_names _ hyinΓ)
        · have hPΔΔ' : Δ ~ Δ' := by
            simp only [HasPerm.perm, List.perm_cons] at hPEy
            exact hPEy
          have h_post' : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ] ~
            ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm.cons
            · apply List.Perm.cons
              exact hPΔΔ'
            · rfl
          have h_post_no_y :=
            HyperEnv.Perm_merge_cancel_right (h_post_subst.symm.trans h_post'.symm)
          have hx_LHS : x ∶ A :: Γ' ∈ ℋ |ₕ [x ∶ A :: Γ'] := by simp
          obtain ⟨Ex, hEx_RHS, hPEx⟩ := HyperEnv.Perm_mem h_post_no_y hx_LHS
          have hxA: (x ∶ A) ∈ Ex := by
            simp only [HasPerm.perm] at hPEx
            have := hPEx.symm.subset
            simp only [List.cons_subset] at this
            exact this.1
          have hxinEx : x ∈ Ex.names := by
            exact Env.mem_pair_fst_in_names _ hxA
          simp only [List.mem_append, List.mem_singleton] at hEx_RHS
          rcases hEx_RHS with h1 | hEx_Xi | rfl
          · cases h1 with
            | inl h =>
              exfalso
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem h) hxinEx]
            | inr h =>
              exfalso
              symm at h
              subst h
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
              apply Or.inl
              use A
              apply (List.Perm.mem_iff (a := (x ∶ A)) hPE).mpr
              simp only [List.mem_cons, Prod.mk.injEq]
              exact Or.inr hxA
          · have hPΓΓ' : Γ ~ Γ' := by
              simp only [HasPerm.perm, List.perm_cons] at hPEx
              exact hPEx
            have h_post'' : ℋ |ₕ [x ∶ A :: Γ] ~
              ℋ |ₕ [x ∶ A :: Γ'] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp only [HasPerm.perm, List.perm_cons] at hPEx
                apply hPEx
              · rfl
            rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_pull_rhs_mid_left
            rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_left
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm_merge_cancel_right (h_post''.trans h_post_no_y.symm)
            · symm
              apply HyperEnv.Perm.cons
              · exact (List.Perm.append_right Δ hPΓΓ').trans
                  (List.Perm.append_left Γ' hPΔΔ')
              · rfl
    · subst hEΓx
      have hzinΓx : (z, ⊥) ∈ x ∶ A :: Γ := by
        simp [HasPerm.perm] at hPE
        have h := hPE.symm.subset
        simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at h
        obtain ⟨hL, hR⟩ := h
        cases hL
        case inl hL1 =>
          rw [hL1.1, hL1.2]
          simp only [List.mem_cons, true_or]
        case inr hL2 =>
          exact List.mem_cons.mpr (Or.inr hL2)
      simp only [List.mem_cons, Prod.mk.injEq] at hzinΓx
      rcases hzinΓx with ⟨hzx, _⟩ | hin
      · subst hzx
        contradiction
      · obtain ⟨Γᵣ, hΓ_split⟩ : ∃ Γᵣ, Γ ~ (z, ⊥) :: Γᵣ := Env.exists_perm_cons hin
        refine ⟨𝒢, (Γᵣ ++ Δ), ?_, ?_⟩
        · apply HyperEnv.Perm.merge_left
          exact (HyperEnv.Perm.cons (List.Perm.append_right Δ hΓ_split) (by rfl))
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
            have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ [x ∶ A :: Γ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
              rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_comm_assoc
            have hP2 : [x ∶ A :: Γ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] ~ [z ∶ ⊥ :: Ξ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
              apply HyperEnv.Perm.cons
              · exact hPE
              · rfl
            have hP3 : [z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            apply HyperEnv.Perm_merge_cancel_left at this
            exact this
          have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
            𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] := by
            have hP1 := h_post.trans (HyperEnv.Perm.merge_right h𝒢ᵣ [Ξ])
            have hP2 : (𝒢 |ₕ [y ∶ Aᗮ :: Δ] |ₕ [Ξ]) ~ 𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] := by
              have hP1 := hPE.symm.trans (List.Perm.cons (x ∶ A) hΓ_split)
              have hP2 : (x ∶ A :: (z, ⊥) :: Γᵣ) ~ ((z, ⊥) :: x ∶ A :: Γᵣ) := List.Perm.swap ..
              have hP3 := (hP1.trans hP2).cons_inv
              apply HyperEnv.Perm.exchange_rhs_left (ℋ := 𝒢 |ₕ [Ξ])
              · apply HyperEnv.Perm_merge_cancel_left_inv
                · exact HyperEnv.Perm.cons hP3 rfl
              apply HyperEnv.Perm_rotate_rhs_right
              simp only [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_comm_assoc_rhs
              rfl
            exact hP1.trans hP2
          have hPΓ' : Γ' ~ Γᵣ := by
            have hin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hEx, hPEx⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hEx
            rcases hEx with h | rfl | rfl
            · cases h
              case inl h𝒢 =>
                exfalso
                have hxA: (x ∶ A) ∈ E := by
                  simp [HasPerm.perm] at hPEx
                  have := hPEx.symm.subset
                  simp only [List.cons_subset] at this
                  exact this.1
                exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
              case inr h =>
                rw [h] at hPEx
                apply List.Perm.cons_inv at hPEx
                simp only [HasPerm.perm]
                exact hPEx.symm
            · exfalso
              simp only [HasPerm.perm] at hPEx
              have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δ := by
                have := hPEx.symm.subset
                simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
                exact this.1
              simp only [List.mem_cons] at hxin
              rcases hxin with heq | hΔ
              · simp only [Prod.mk.injEq] at heq
                exact hneq heq.1
              · exact hxΔ (Env.mem_pair_fst_in_names _ hΔ)
          have hPΔ' : Δ' ~ Δ := by
            have hin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hEy, hPEy⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hEy
            rcases hEy with h | rfl | rfl
            · cases h
              case inl h𝒢 =>
                exfalso
                have hyA: (y ∶ Aᗮ) ∈ E := by
                  simp only [HasPerm.perm] at hPEy
                  have := hPEy.symm.subset
                  simp only [List.cons_subset] at this
                  exact this.1
                exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
              case inr h =>
                exfalso
                subst h
                simp only [HasPerm.perm] at hPEy
                have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γᵣ := by
                  have := hPEy.symm.subset
                  simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
                  exact this.1
                simp only [List.mem_cons] at hyin
                rcases hyin with heq | hΔ
                · simp only [Prod.mk.injEq] at heq
                  exact hneq heq.1.symm
                · apply hyΓ
                  have := (Env.mem_pair_fst_in_names _ hΔ)
                  rw [Env.mem_pair_fst_in_names_iff] at this
                  obtain ⟨T, hΓᵣ⟩ := this
                  have hΓᵣz : (y, T) ∈ (z, ⊥) :: Γᵣ :=
                    List.mem_cons_of_mem _ hΓᵣ
                  have hinΓ : (y, T) ∈ Γ :=
                    (List.Perm.mem_iff hΓ_split.symm).mp hΓᵣz
                  rw [Env.mem_pair_fst_in_names_iff]
                  exact ⟨T, hinΓ⟩
            · simp only [HasPerm.perm, List.perm_cons] at hPEy ⊢
              exact hPEy.symm
          have hPℋ𝒢 : ℋ ~ 𝒢 := by
            have hPx : x ∶ A :: Γ' ~ x ∶ A :: Γᵣ := by
              have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']  := by simp
              obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with _ | rfl | rfl
              · exact Env.Perm.cons hPΓ'
              · exact Env.Perm.cons hPΓ'
            have hPy : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δ := by
              have hyin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
              obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hyin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with _ | rfl | rfl
              · exact Env.Perm.cons hPΔ'
              · exact Env.Perm.cons hPΔ'
            have hP1 : 𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] ~
              𝒢 |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
              apply HyperEnv.Perm.merge
              · exact HyperEnv.Perm.merge rfl (HyperEnv.Perm.cons hPx.symm rfl)
              · exact (HyperEnv.Perm.cons hPy.symm rfl)
            have hP2 := h_post_subst.trans hP1
            apply HyperEnv.Perm_merge_cancel_right at hP2
            apply HyperEnv.Perm_merge_cancel_right at hP2
            exact hP2
          exact HyperEnv.Perm.merge hPℋ𝒢 (HyperEnv.Perm.cons (List.Perm.append hPΓ' hPΔ') rfl)
  · have hzinΔy : (z, ⊥) ∈ y ∶ Aᗮ :: Δ := by
      simp [HasPerm.perm] at hPE
      have h := hPE.symm.subset
      simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at h
      obtain ⟨hL, hR⟩ := h
      cases hL
      case inl hL1 =>
        rw [hL1.1, hL1.2]
        simp
      case inr hL2 =>
        exact List.mem_cons.mpr (Or.inr hL2)
    simp only [List.mem_cons, Prod.mk.injEq] at hzinΔy
    rcases hzinΔy with ⟨hzy, _⟩ | hin
    · subst hzy
      contradiction
    · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (z, ⊥) :: Δᵣ := Env.exists_perm_cons hin
      refine ⟨𝒢, (Γ ++ Δᵣ), ?_, ?_⟩
      · apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.cons
        · have hP1 := List.Perm.append_right Γ hΔ_split
          have hP2 : Γ ++ Δ ~ Δ ++ Γ := by
            simp only [HasPerm.perm]
            apply List.perm_append_comm
          have hP3 : ((z, ⊥) :: Δᵣ ++ Γ) ~ ((z, ⊥) :: Γ ++ Δᵣ) := by
            apply List.Perm.cons
            exact List.perm_append_comm
          exact (hP2.trans hP1).trans hP3
        · rfl
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [x ∶ A :: Γ] := by
          have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ [y ∶ Aᗮ :: Δ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ]  := by
            apply HyperEnv.Perm_rotate_rhs_left
            rfl
          have hP2 : [y ∶ Aᗮ :: Δ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ] ~ [z ∶ ⊥ :: Ξ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ] := by
            apply HyperEnv.Perm.cons
            · exact hPE
            · rfl
          have hP3 : [z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := HyperEnv.Perm.merge_comm
          have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
          apply HyperEnv.Perm_merge_cancel_left at this
          exact this
        have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
          𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] := by
          have hP1 := h_post.trans (HyperEnv.Perm.merge_right h𝒢ᵣ [Ξ])
          have hP2 : (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [Ξ]) ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] := by
            have hP1 := hPE.symm.trans (List.Perm.cons (y ∶ Aᗮ) hΔ_split)
            have hP2 : (y ∶ Aᗮ :: (z, ⊥) :: Δᵣ) ~ ((z, ⊥) :: y ∶ Aᗮ :: Δᵣ) := List.Perm.swap ..
            have hP3 := (hP1.trans hP2).cons_inv
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm.merge rfl rfl
            · exact HyperEnv.Perm.cons hP3 rfl
          exact hP1.trans hP2
        have hPΓ' : Γ' ~ Γ := by
          have hin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hEx, hPEx⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
          simp only [List.mem_append, List.mem_singleton] at hEx
          rcases hEx with h | rfl | rfl
          · cases h
            case inl h𝒢 =>
              exfalso
              have hxA: (x ∶ A) ∈ E := by
                simp [HasPerm.perm] at hPEx
                have := hPEx.symm.subset
                simp only [List.cons_subset] at this
                exact this.1
              exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
            case inr h =>
              rw [h] at hPEx
              apply List.Perm.cons_inv at hPEx
              simp only [HasPerm.perm]
              exact hPEx.symm
          · exfalso
            simp [HasPerm.perm] at hPEx
            have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δᵣ := by
              have := hPEx.symm.subset
              simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
              exact this.1
            simp only [List.mem_cons] at hxin
            rcases hxin with heq | hΔ
            · simp only [Prod.mk.injEq] at heq
              exact hneq heq.1
            · apply hxΔ
              have := (Env.mem_pair_fst_in_names _ hΔ)
              rw [Env.mem_pair_fst_in_names_iff] at this
              obtain ⟨T, hΔᵣz⟩ := this
              have hΔᵣz : (x, T) ∈ (z, ⊥) :: Δᵣ := by
                apply List.mem_cons_of_mem _ hΔᵣz
              have hinΔ : (x, T) ∈ Δ :=
                (List.Perm.mem_iff hΔ_split.symm).mp hΔᵣz
              rw [Env.mem_pair_fst_in_names_iff]
              exact ⟨T, hinΔ⟩
        have hPΔ' : Δ' ~ Δᵣ := by
          have hin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hEy, hPEy⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
          simp only [List.mem_append, List.mem_singleton] at hEy
          rcases hEy with h | rfl | rfl
          · cases h
            case inl h𝒢 =>
              exfalso
              have hyA: (y ∶ Aᗮ) ∈ E := by
                simp [HasPerm.perm] at hPEy
                have := hPEy.symm.subset
                simp only [List.cons_subset] at this
                exact this.1
              exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
            case inr h =>
              exfalso
              subst h
              simp [HasPerm.perm] at hPEy
              have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γ := by
                have := hPEy.symm.subset
                simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
                exact this.1
              simp only [List.mem_cons] at hyin
              rcases hyin with heq | hΔ
              · simp only [Prod.mk.injEq] at heq
                exact hneq heq.1.symm
              · apply hyΓ
                have := (Env.mem_pair_fst_in_names _ hΔ)
                rw [Env.mem_pair_fst_in_names_iff] at this
                obtain ⟨T, hΔᵣ⟩ := this
                exact (Env.mem_pair_fst_in_names _ hΔᵣ)
          · simp only [HasPerm.perm, List.perm_cons] at hPEy ⊢
            exact hPEy.symm
        have hPℋ𝒢 : ℋ ~ 𝒢 := by
          have hPx : x ∶ A :: Γ' ~ x ∶ A :: Γ := by
            have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']  := by simp
            obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with _ | rfl | rfl
            · exact Env.Perm.cons hPΓ'
            · exact Env.Perm.cons hPΓ'
          have hPy : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δᵣ := by
            have hyin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hyin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with _ | rfl | rfl
            · exact Env.Perm.cons hPΔ'
            · exact Env.Perm.cons hPΔ'
          have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] ~
            𝒢 |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm.merge rfl (HyperEnv.Perm.cons hPx.symm rfl)
            · exact (HyperEnv.Perm.cons hPy.symm rfl)
          have hP2 := h_post_subst.trans hP1
          apply HyperEnv.Perm_merge_cancel_right at hP2
          apply HyperEnv.Perm_merge_cancel_right at hP2
          exact hP2
        exact HyperEnv.Perm.merge hPℋ𝒢 (HyperEnv.Perm.cons (List.Perm.append hPΓ' hPΔ') rfl)
