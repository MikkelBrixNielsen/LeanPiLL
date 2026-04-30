import PiLL.Model.Environment

set_option linter.style.setOption false
set_option linter.flexible false
-- same reason as in Environment.lean

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
            simp at this
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
              simp
              apply Or.inl
              use Aᗮ
              apply (List.Perm.mem_iff (a := (y ∶ Aᗮ)) hPE).mpr
              simp
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
            simp [HasPerm.perm] at hPEy
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
            simp [HasPerm.perm] at hPEx
            have := hPEx.symm.subset
            simp at this
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
              simp
              apply Or.inl
              use A
              apply (List.Perm.mem_iff (a := (x ∶ A)) hPE).mpr
              simp
              exact Or.inr hxA
          · have hPΓΓ' : Γ ~ Γ' := by
              simp [HasPerm.perm] at hPEx
              exact hPEx
            have h_post'' : ℋ |ₕ [x ∶ A :: Γ] ~
              ℋ |ₕ [x ∶ A :: Γ'] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp [HasPerm.perm] at hPEx
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
        simp at h
        obtain ⟨hL, hR⟩ := h
        cases hL
        case inl hL1 =>
          rw [hL1.1, hL1.2]
          simp
        case inr hL2 =>
          exact List.mem_cons.mpr (Or.inr hL2)
      simp at hzinΓx
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
                  simp at this
                  exact this.1
                exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
              case inr h =>
                rw [h] at hPEx
                apply List.Perm.cons_inv at hPEx
                simp [HasPerm.perm]
                exact hPEx.symm
            · exfalso
              simp [HasPerm.perm] at hPEx
              have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δ := by
                have := hPEx.symm.subset
                simp at this ⊢
                exact this.1
              simp only [List.mem_cons] at hxin
              rcases hxin with heq | hΔ
              · simp at heq
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
                  simp [HasPerm.perm] at hPEy
                  have := hPEy.symm.subset
                  simp at this
                  exact this.1
                exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
              case inr h =>
                exfalso
                subst h
                simp [HasPerm.perm] at hPEy
                have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γᵣ := by
                  have := hPEy.symm.subset
                  simp at this ⊢
                  exact this.1
                simp only [List.mem_cons] at hyin
                rcases hyin with heq | hΔ
                · simp at heq
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
            · simp [HasPerm.perm] at hPEy ⊢
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
      simp at h
      obtain ⟨hL, hR⟩ := h
      cases hL
      case inl hL1 =>
        rw [hL1.1, hL1.2]
        simp
      case inr hL2 =>
        exact List.mem_cons.mpr (Or.inr hL2)
    simp at hzinΔy
    rcases hzinΔy with ⟨hzy, _⟩ | hin
    · subst hzy
      contradiction
    · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (z, ⊥) :: Δᵣ := Env.exists_perm_cons hin
      refine ⟨𝒢, (Γ ++ Δᵣ), ?_, ?_⟩
      · apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.cons
        · have hP1 := List.Perm.append_right Γ hΔ_split
          have hP2 : Γ ++ Δ ~ Δ ++ Γ := by
            simp [HasPerm.perm]
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
                simp at this
                exact this.1
              exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
            case inr h =>
              rw [h] at hPEx
              apply List.Perm.cons_inv at hPEx
              simp [HasPerm.perm]
              exact hPEx.symm
          · exfalso
            simp [HasPerm.perm] at hPEx
            have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δᵣ := by
              have := hPEx.symm.subset
              simp at this ⊢
              exact this.1
            simp only [List.mem_cons] at hxin
            rcases hxin with heq | hΔ
            · simp at heq
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
                simp at this
                exact this.1
              exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
            case inr h =>
              exfalso
              subst h
              simp [HasPerm.perm] at hPEy
              have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γ := by
                have := hPEy.symm.subset
                simp at this ⊢
                exact this.1
              simp only [List.mem_cons] at hyin
              rcases hyin with heq | hΔ
              · simp at heq
                exact hneq heq.1.symm
              · apply hyΓ
                have := (Env.mem_pair_fst_in_names _ hΔ)
                rw [Env.mem_pair_fst_in_names_iff] at this
                obtain ⟨T, hΔᵣ⟩ := this
                exact (Env.mem_pair_fst_in_names _ hΔᵣ)
          · simp [HasPerm.perm] at hPEy ⊢
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

lemma HyperEnv.Perm.extract_one_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {u v x y : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [u ∶ A :: Γ'] |ₕ [v ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (hvΓ : v ∉ Γ.names) (huΔ : u ∉ Δ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by
  have hxin : ([x ∶ 1]) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hxin
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' := h𝒢_split.trans (HyperEnv.Perm.cons hPE (.refl _))
      have h_pre_bot : 𝒢ᵣ' |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ] := by
        have := HyperEnv.Perm.merge_right h𝒢' ([u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ])
        rw [← HyperEnv.merge_assoc] at this
        have := this.symm.trans h_pre
        apply HyperEnv.Perm_rotate_rhs_right at this
        rw [HyperEnv.merge_assoc, ← HyperEnv.cons_append, ← HyperEnv.cons_append] at this
        apply HyperEnv.Perm.cons_cancel_left at this
        rw [← HyperEnv.merge_nilR (𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ])]
        apply HyperEnv.Perm_rotate_rhs_left
        simp only [List.append_eq, List.cons_append, List.nil_append,
          List.append_assoc, List.append_nil] at ⊢ this
        exact this
      simp only [HasPerm.perm, List.perm_singleton] at hPE
      subst hPE
      have hFuᵣ : u ∉ HyperEnv.names 𝒢ᵣ':= by
        intro hc
        exact hFu (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
      have hFvᵣ : v ∉ HyperEnv.names 𝒢ᵣ' := by
        intro hc
        exact hFv (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
      obtain ⟨𝒢ᵣ'', Γₙ, h_pre', h_post'⟩ :=
        HyperEnv.Perm.extract_bot_res h_pre_bot h_post hyu hyv hFuᵣ hFvᵣ hFu' hFv' hneq huΔ hvΓ
      refine ⟨𝒢ᵣ'', Γₙ, ?_, h_post'⟩
      · have h1 := HyperEnv.Perm.merge_right h𝒢_split ([Γ‚ Δ])
        have h2 := HyperEnv.Perm.merge_right h_pre' ([[x ∶ 1]])
        conv_rhs at h1 => rw [HyperEnv.cons_append]
        apply HyperEnv.Perm_rotate_rhs_right at h1
        conv_rhs at h2 => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h2
        rw [← HyperEnv.merge_assoc] at h2
        apply HyperEnv.Perm_rotate_rhs_right at h2
        exact h1.trans h2
    case inr h =>
      subst h
      simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
      obtain ⟨⟨h1, _⟩, _⟩ := hPE
      subst h1
      contradiction
  · simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
    obtain ⟨⟨h1, _⟩, _⟩ := hPE
    subst h1
    contradiction

lemma HyperEnv.Perm.extract_tensor_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Γ'' Δ Δ' Δ'' : Env} {u v x w : FPName} {A B C : Types}
  (h_pre : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ])
  (h_post : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~ 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ])
  (hxw : x ≠ w) (hux : u ≠ x) (huw : u ≠ w) (hvx : v ≠ x) (hvw : v ≠ w)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (huΔ' : u ∉ Δ'.names) (hvΓ' : v ∉ Γ'.names) :
   ∃ 𝒢ₙ Γₙ Δₙ,
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ] ∧
    ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [w ∶ A :: Γₙ] |ₕ [x ∶ B :: Δₙ] := by
  have h1 : (x ∶ A ⨂ B :: Γ‚ Δ) ∈ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | hh
  · rcases h with hE𝒢 | hEΓu
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ξz : 𝒢 ~ (x ∶ A ⨂ B :: Γ‚ Δ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ'‚ Δ'], Γ, Δ, ?_, ?_⟩
      · apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        rw [← HyperEnv.cons_append]
        exact h𝒢Ξz
      · have h_pre_subst : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] ~
          ([x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ') |ₕ ([u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ']) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ξz h_pre
          exact this.symm
        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        simp only [HyperEnv.merge_assoc] at h_post
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post
        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst
        have hEv : v ∶ Cᗮ :: Δ'' ∈ ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by simp
        obtain ⟨Ey, hEy', hPEy⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hEv
        have hyC : (v ∶ Cᗮ) ∈ Ey := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEy).mpr (by simp)
        have hyinEy : v ∈ Ey.names := Env.mem_pair_fst_in_names _ hyC
        simp only [List.mem_append, List.mem_singleton] at hEy'
        rcases hEy' with h1 | rfl | rfl | rfl
        · cases h1 with
          | inl h1' =>
            cases h1' with
            | inl hin𝒢ᵣ =>
              exfalso
              apply hFv
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem hin𝒢ᵣ) hyinEy]
            | inr hEyΞ =>
              rcases hEyΞ with rfl | rfl
              · simp at hyinEy
                rcases hyinEy with rfl | h2
                · exfalso ; apply hvw ; rfl
                · exfalso
                  have ⟨hΓsub, _⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFv (hΓsub (Env.mem_pair_fst_in_names_iff.mpr h2))
              · simp at hyinEy
                rcases hyinEy with rfl | h2
                · exfalso ; apply hvx ; rfl
                · exfalso
                  have ⟨_, hΔsub⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFv (hΔsub (Env.mem_pair_fst_in_names_iff.mpr h2))
          | inr hEyΓx =>
            exfalso
            symm at hEyΓx
            subst hEyΓx
            simp only [List.mem_cons] at hyC
            rcases hyC with heq | hyinΓ
            · injection heq with heq_name _
              exact hneq heq_name.symm
            · exact hvΓ' (Env.mem_pair_fst_in_names _ hyinΓ)
        · have hPΔ'Δ'' : Δ' ~ Δ'' := by
            simp [HasPerm.perm] at hPEy
            exact hPEy
          have h_post' : ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ']) ~
            ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm_merge_cancel_left_inv
            rw [HyperEnv.Perm_singleton_singleton]
            apply List.Perm.cons
            exact hPΔ'Δ''
          have h_post_no_v := by
            have ht := h_post_subst.symm.trans h_post'.symm
            simp only [← HyperEnv.merge_assoc] at ht
            apply HyperEnv.Perm_merge_cancel_right at ht
            exact ht
          have huRHS : u ∶ C :: Γ'' ∈ ℋ |ₕ [u ∶ C :: Γ''] := by simp
          obtain ⟨Eu, hEuLHS, hPEu⟩ := HyperEnv.Perm_mem h_post_no_v huRHS
          have huinEu : u ∈ Eu.names := by
            have huC: (u ∶ C) ∈ Eu := by
              simp [HasPerm.perm] at hPEu
              have := hPEu.symm.subset
              simp at this
              exact this.1
            exact Env.mem_pair_fst_in_names _ huC
          simp only [List.mem_append, List.mem_singleton] at hEuLHS
          rcases hEuLHS with h1 | hExΞ | rfl
          · cases h1 with
            | inl h =>
              exfalso
              apply hFu
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              rcases h with hin | rfl
              · simp [(HyperEnv.subset_names_of_mem hin) huinEu]
              · exfalso
                simp at huinEu
                rcases huinEu with rfl | hin
                · apply huw ; rfl
                · have ⟨hΓ, _⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFu (hΓ (Env.mem_pair_fst_in_names_iff.mpr hin))
            | inr h =>
              exfalso
              subst h
              simp at huinEu
              rcases huinEu with rfl | hin
              · apply hux ; rfl
              · have ⟨_, hΔ⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                exact hFu (hΔ (Env.mem_pair_fst_in_names_iff.mpr hin))
          · have hPΓ'Γ'' : Γ' ~ Γ'' := by
              simp [HasPerm.perm] at hPEu
              exact hPEu
            have h_post'' : ℋ |ₕ [u ∶ C :: Γ'] ~
              ℋ |ₕ [u ∶ C :: Γ''] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp [HasPerm.perm] at hPEu
                apply hPEu
              · rfl
            have ht := h_post''.trans h_post_no_v.symm
            apply HyperEnv.Perm_merge_cancel_right at ht
            rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm_rotate_rhs_right
              exact ht
            · symm
              apply HyperEnv.Perm.cons
              · exact (List.Perm.append_right Δ' hPΓ'Γ'').trans
                  (List.Perm.append_left Γ'' hPΔ'Δ'')
              · rfl
    · subst hEΓu
      have hxin := (List.Perm.mem_iff (a := x ∶ A ⨂ B) hPE).mpr (by simp)
      simp at hxin
      rcases hxin with ⟨rfl, rfl⟩ | h
      · exfalso ; apply hux ; rfl
      · obtain ⟨Ξ, hPΓ'⟩ : ∃ Ξ, Γ' ~ (x, A ⨂ B) :: Ξ :=
          Env.exists_perm_cons h
        have hPE_no_x : u ∶ C :: Ξ ~ Γ‚ Δ := by
          have h1 := hPE.symm.trans (List.Perm.cons (u ∶ C) hPΓ')
          have h2 : (u ∶ C :: (x, A ⨂ B) :: Ξ) ~ ((x, A ⨂ B) :: u ∶ C :: Ξ) := List.Perm.swap ..
          exact (h1.trans h2).cons_inv.symm
        have huin : (u, C) ∈ Γ‚ Δ :=
          (List.Perm.mem_iff (a := u ∶ C) hPE_no_x ).mp (by simp)
        simp at huin
        rcases huin with huΓ | huΔ
        · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (u, C) :: Γᵣ := Env.exists_perm_cons huΓ
          have hPΞ : Ξ ~ Γᵣ‚ Δ := List.Perm.cons_inv (hPE_no_x.trans (List.Perm.append_right Δ hPΓ))
          refine ⟨𝒢, (Γᵣ‚ Δ'), Δ, ?_, ?_⟩
          · apply HyperEnv.Perm.merge
            · rfl
            · apply HyperEnv.Perm_singleton_singleton.mpr
              rw [← List.cons_append]
              have hP1 : x ∶ A ⨂ B :: Γᵣ‚ Δ‚ Δ' ~ x ∶ A ⨂ B :: Γᵣ‚ Δ'‚ Δ := by
                simp
                apply List.Perm.cons
                apply List.Perm.append_left
                exact List.perm_append_comm
              have hP2 := List.Perm.append (t₂ := Δ') (by
                have : (x ∶ A ⨂ B :: Ξ) ~ (x ∶ A ⨂ B :: Γᵣ‚ Δ) := by
                  apply List.Perm.cons
                  exact hPΞ
                exact hPΓ'.trans this) (by rfl)
              exact hP2.trans hP1
          · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
                [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_comm_assoc
              have hP2 : [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] ~
                [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                apply HyperEnv.Perm.cons hPE rfl
              have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
                HyperEnv.Perm.merge_comm
              have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
              exact HyperEnv.Perm_merge_cancel_left this
            have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [v ∶ Cᗮ :: Δ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
            have hPΔ'' : Δ'' ~ Δ' := by
              have hin : (v ∶ Cᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
              obtain ⟨E, hE, hPEv⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with h | rfl | h_wx
              · rcases h with h𝒢 | rfl
                · rcases h𝒢 with h1 | h2
                  · exfalso
                    have hvA: (v ∶ Cᗮ) ∈ E := (List.Perm.mem_iff hPEv).mpr (by simp)
                    exact hFv (HyperEnv.subset_names_of_mem h1
                      (Env.mem_pair_fst_in_names _ hvA))
                  · rw [h2] at hPEv
                    apply List.Perm.cons_inv at hPEv
                    exact hPEv.symm
                · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                  simp at hvin
                  rcases hvin with ⟨rfl, rfl⟩ | hvΓ
                  · exfalso ; apply hvw ; rfl
                  · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΓ]
                    have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                      (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                    simp at hin2
                    exfalso
                    rcases hin2 with ⟨rfl, _⟩ | hvΞ
                    · apply hneq ; rfl
                    · have h3 : (v, Cᗮ) ∈ Γ' :=
                        (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                      exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
              · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                simp at hvin
                exfalso
                rcases hvin with ⟨rfl, rfl⟩ | hvΔ
                · apply hvx  ; rfl
                · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΔ]
                  have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                    (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                  simp at hin2
                  rcases hin2 with ⟨rfl, _⟩ | hvΞ
                  · apply hneq ; rfl
                  · have h3 : (v, Cᗮ) ∈ Γ' :=
                      (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
            have h_post_no_v : ℋ |ₕ [u ∶ C :: Γ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_rotate_rhs_right at h_post_subst
              rw [← HyperEnv.merge_assoc] at h_post_subst
              have : [v ∶ Cᗮ :: Δ''] ~ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact Env.Perm.cons hPΔ''
              have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _) this
              exact HyperEnv.Perm_merge_cancel_right (hLHS.symm.trans (h_post_subst))
            have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := u ∶ C :: Γ'')
              h_post_no_v.symm (by simp)
            simp at hE1
            rcases hE1 with h𝒢 | rfl | rfl
            · exfalso
              have huΓ := (List.Perm.mem_iff (a := u ∶ C) hPE1).mpr (by simp)
              exact hFu (HyperEnv.mem_of_mem_mem_names huΓ h𝒢)
            · have hPΓ'' : Γ'' ~ w ∶ A :: Γᵣ := by
                have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) hPΓ)
                have h2 : (w ∶ A :: u ∶ C :: Γᵣ) ~ (u ∶ C :: w ∶ A :: Γᵣ) := List.Perm.swap ..
                exact List.Perm.cons_inv (h1.trans h2)
              have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] := by
                have : 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [u ∶ C :: Γ''] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm.merge
                  · apply HyperEnv.Perm.merge_comm
                  · rw [HyperEnv.Perm_singleton_singleton]
                    exact hPE1.symm
                exact HyperEnv.Perm_merge_cancel_right (h_post_no_v.trans this.symm)
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm.merge
              · exact hℋ.trans HyperEnv.Perm.merge_comm
              · rw [HyperEnv.Perm_singleton_singleton]
                rw [← List.cons_append, Env.merge]
                exact List.Perm.append hPΓ'' hPΔ''
            · exfalso
              have h_post_subst2 : ℋ |ₕ [u ∶ C :: Γ''] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                    (HyperEnv.Perm_singleton_singleton.mpr hPE1)
                exact h_post_no_v.trans this
              have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := HyperEnv.Perm_merge_cancel_right h_post_subst2
              have hwin: w ∶ A :: Γ ∈ 𝒢 |ₕ [w ∶ A :: Γ] := by simp
              obtain ⟨E, hE, hPEw⟩ := HyperEnv.Perm_mem hℋ hwin
              have huEw : u ∶ C ∈ w ∶ A :: Γ := List.mem_cons_of_mem _ huΓ
              have huE := (List.Perm.mem_iff (a := u ∶ C) hPEw).mpr huEw
              exact hFu' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ huE))
        · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (u, C) :: Δᵣ := Env.exists_perm_cons huΔ
          have hPΞ : Ξ ~ Γ‚ Δᵣ := by
            have h1 := hPE_no_x.trans (List.Perm.append_left Γ hΔ_split)
            exact List.Perm.cons_inv (h1.trans List.perm_middle)
          refine ⟨𝒢, Γ, (Δᵣ ++ Δ'), ?_, ?_⟩
          · apply HyperEnv.Perm.merge_left
            apply HyperEnv.Perm.cons
            · have h1 := List.Perm.append_right Δ' hPΓ'
              have h2 : ((x, A ⨂ B) :: Ξ) ++ Δ' ~ (x, A ⨂ B) :: (Ξ ++ Δ') := by rfl
              have h3 : (x, A ⨂ B) :: (Ξ ++ Δ') ~ (x, A ⨂ B) :: ((Γ ++ Δᵣ) ++ Δ') :=
                List.Perm.cons _ (List.Perm.append_right Δ' hPΞ)
              have h4 : (x, A ⨂ B) :: ((Γ ++ Δᵣ) ++ Δ') ~ (x, A ⨂ B) :: (Γ ++ (Δᵣ ++ Δ')) := by
                rw [List.append_assoc]
              exact h1.trans (h2.trans (h3.trans h4))
            · rfl
          · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
                [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_comm_assoc
              have hP2 : [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] ~
                [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                apply HyperEnv.Perm.cons hPE rfl
              have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
                HyperEnv.Perm.merge_comm
              have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
              exact HyperEnv.Perm_merge_cancel_left this
            have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [v ∶ Cᗮ :: Δ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
            have hPΔ'' : Δ'' ~ Δ' := by
              have hin : (v ∶ Cᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
              obtain ⟨E, hE, hPEv⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with h | rfl | h_wx
              · rcases h with h𝒢 | rfl
                · rcases h𝒢 with h1 | h2
                  · exfalso
                    have hvA: (v ∶ Cᗮ) ∈ E := (List.Perm.mem_iff hPEv).mpr (by simp)
                    exact hFv (HyperEnv.subset_names_of_mem h1
                      (Env.mem_pair_fst_in_names _ hvA))
                  · rw [h2] at hPEv
                    apply List.Perm.cons_inv at hPEv
                    exact hPEv.symm
                · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                  simp at hvin
                  rcases hvin with ⟨rfl, rfl⟩ | hvΓ
                  · exfalso ; apply hvw ; rfl
                  · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΓ]
                    have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                      (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                    simp at hin2
                    exfalso
                    rcases hin2 with ⟨rfl, _⟩ | hvΞ
                    · apply hneq ; rfl
                    · have h3 : (v, Cᗮ) ∈ Γ' :=
                        (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                      exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
              · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                simp at hvin
                exfalso
                rcases hvin with ⟨rfl, rfl⟩ | hvΔ
                · apply hvx  ; rfl
                · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΔ]
                  have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                    (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                  simp at hin2
                  rcases hin2 with ⟨rfl, _⟩ | hvΞ
                  · apply hneq ; rfl
                  · have h3 : (v, Cᗮ) ∈ Γ' :=
                      (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
            have h_post_no_v : ℋ |ₕ [u ∶ C :: Γ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_rotate_rhs_right at h_post_subst
              rw [← HyperEnv.merge_assoc] at h_post_subst
              have : [v ∶ Cᗮ :: Δ''] ~ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact Env.Perm.cons hPΔ''
              have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _) this
              exact HyperEnv.Perm_merge_cancel_right (hLHS.symm.trans (h_post_subst))
            have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := u ∶ C :: Γ'')
              h_post_no_v.symm (by simp)
            simp at hE1
            rcases hE1 with h𝒢 | rfl | rfl
            · exfalso
              have huΔ := (List.Perm.mem_iff (a := u ∶ C) hPE1).mpr (by simp)
              exact hFu (HyperEnv.mem_of_mem_mem_names huΔ h𝒢)
            · exfalso
              have h_post_subst2 : ℋ |ₕ [u ∶ C :: Γ''] ~
                𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] :=
                  HyperEnv.Perm.merge
                    (HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                      (HyperEnv.Perm_singleton_singleton.mpr hPE1))
                    (HyperEnv.Perm.refl _)
                exact h_post_no_v.trans this
              have hRHS_rot : 𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [x ∶ B :: Δ] |ₕ [u ∶ C :: Γ''] := by
                symm
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm.trans (HyperEnv.Perm.merge_comm).symm
                rfl
              have hℋ := HyperEnv.Perm_merge_cancel_right (h_post_subst2.trans hRHS_rot)
              have hxin: x ∶ B :: Δ ∈ 𝒢 |ₕ [x ∶ B :: Δ] := by simp
              obtain ⟨E, hE, hPEx⟩ := HyperEnv.Perm_mem hℋ hxin
              have huEx : u ∶ C ∈ x ∶ B :: Δ := List.mem_cons_of_mem _ huΔ
              have huE := (List.Perm.mem_iff (a := u ∶ C) hPEx).mpr huEx
              exact hFu' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ huE))
            · have hPΓ'' : Γ'' ~ x ∶ B :: Δᵣ := by
                have h1 := hPE1.symm.trans (List.Perm.cons (x ∶ B) hΔ_split)
                have h2 : (x ∶ B :: u ∶ C :: Δᵣ) ~ (u ∶ C :: x ∶ B :: Δᵣ) := List.Perm.swap ..
                exact List.Perm.cons_inv (h1.trans h2)
              have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] := by
                  apply HyperEnv.Perm.merge
                  · rfl
                  · rw [HyperEnv.Perm_singleton_singleton]
                    exact hPE1
                exact HyperEnv.Perm_merge_cancel_right (h_post_no_v.trans this)
              apply HyperEnv.Perm.merge
              · exact hℋ
              · rw [HyperEnv.Perm_singleton_singleton]
                rw [← List.cons_append]
                exact List.Perm.append hPΓ'' hPΔ''
  · subst hh
    have hxin := (List.Perm.mem_iff (a := x ∶ A ⨂ B) hPE).mpr (by simp)
    simp at hxin
    rcases hxin with ⟨rfl, _⟩ | h
    · exfalso ; apply hvx ; rfl
    · obtain ⟨Ξ, hPΔ'⟩ : ∃ Ξ, Δ' ~ (x, A ⨂ B) :: Ξ := Env.exists_perm_cons h
      have hPE_no_x : v ∶ Cᗮ :: Ξ ~ Γ‚ Δ := by
        have h1 := hPE.symm.trans (List.Perm.cons (v ∶ Cᗮ) hPΔ')
        have h2 : (v ∶ Cᗮ :: (x, A ⨂ B) :: Ξ) ~ ((x, A ⨂ B) :: v ∶ Cᗮ :: Ξ) := List.Perm.swap ..
        exact (h1.trans h2).cons_inv.symm
      have hvin : (v, Cᗮ) ∈ Γ‚ Δ :=
        (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE_no_x ).mp (by simp)
      simp at hvin
      rcases hvin with hΓ | hΔ
      · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (v, Cᗮ) :: Γᵣ := Env.exists_perm_cons hΓ
        have hPΞ : Ξ ~ Γᵣ‚ Δ := List.Perm.cons_inv (hPE_no_x.trans (List.Perm.append_right Δ hPΓ))
        refine ⟨𝒢, (Γ'‚ Γᵣ), Δ, ?_, ?_⟩
        · apply HyperEnv.Perm.merge
          · rfl
          · apply HyperEnv.Perm_singleton_singleton.mpr
            have hP1 : x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ ~ x ∶ A ⨂ B :: Γ'‚ Ξ := by
              apply List.Perm.cons
              rw [Env.merge_assoc]
              apply List.Perm.append
              · rfl
              · exact hPΞ.symm
            have hP2 : x ∶ A ⨂ B :: Γ'‚ Ξ ~ Γ'‚ (x ∶ A ⨂ B :: Ξ) := List.perm_middle.symm
            have hP3 : Γ'‚ (x ∶ A ⨂ B :: Ξ) ~ Γ'‚ Δ' := by
              apply List.Perm.append
              · rfl
              · exact hPΔ'.symm
            exact ((hP1.trans hP2).trans hP3).symm
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
              [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.merge_assoc]
            have hP2 : [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] ~
              [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm.cons hPE rfl
            have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
              HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            exact HyperEnv.Perm_merge_cancel_left this
          have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [u ∶ C :: Γ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
          have hPΓ'' : Γ'' ~ Γ' := by
            have hin : (u ∶ C :: Γ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
            obtain ⟨E, hE, hPEu⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with h | rfl | hwx
            · rcases h with h𝒢 | rfl
              · rcases h𝒢 with h1 | h2
                · exfalso
                  have huA: (u ∶ C) ∈ E := (List.Perm.mem_iff hPEu).mpr (by simp)
                  exact hFu (HyperEnv.subset_names_of_mem h1 (Env.mem_pair_fst_in_names _ huA))
                · rw [h2] at hPEu
                  exact (List.Perm.cons_inv hPEu).symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
                simp at huin
                rcases huin with ⟨rfl, rfl⟩ | huΓ
                · apply huw ; rfl
                · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΓ])
                  simp at huin
                  rcases huin with ⟨rfl, _⟩ | huΞ
                  · apply hneq ; rfl
                  · apply huΔ'
                    apply Env.mem_pair_fst_in_names_iff.mpr
                    use C
                    exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, rfl⟩ | huΔ
              · apply hux ; rfl
              · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΔ])
                simp at huin
                rcases huin with ⟨rfl, _⟩ | huΞ
                · apply hneq ; rfl
                · apply huΔ'
                  apply Env.mem_pair_fst_in_names_iff.mpr
                  use C
                  exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
          have h_post_no_u : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have hPeq : [u ∶ C :: Γ''] ~ [u ∶ C :: Γ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact Env.Perm.cons hPΓ''
            have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ''] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPeq)
                (HyperEnv.Perm.refl _)
            have hP1 := h_post_subst.symm.trans hLHS
            apply HyperEnv.Perm_rotate_rhs_left at hP1
            symm at hP1
            apply HyperEnv.Perm_rotate_rhs_right at hP1
            rw [← HyperEnv.merge_assoc] at hP1
            have hP2 := HyperEnv.Perm_merge_cancel_right hP1
            apply HyperEnv.Perm_rotate_rhs_left at hP2
            symm at hP2
            exact (hP2.trans HyperEnv.Perm.merge_comm).symm
          have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := v ∶ Cᗮ :: Δ'') h_post_no_u.symm (by simp)
          simp at hE1
          rcases hE1 with h𝒢 | rfl | rfl
          · exfalso
            have hvΓ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE1).mpr (by simp)
            exact hFv (HyperEnv.mem_of_mem_mem_names hvΓ h𝒢)
          · have hPΔ'' : Δ'' ~ w ∶ A :: Γᵣ := by
              have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) hPΓ)
              have h2 : (w ∶ A :: v ∶ Cᗮ :: Γᵣ) ~ (v ∶ Cᗮ :: w ∶ A :: Γᵣ) := List.Perm.swap ..
              exact List.Perm.cons_inv (h1.trans h2)
            have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] := by
              have : 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Cᗮ :: Δ''] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm.merge
                · apply HyperEnv.Perm.merge_comm
                · rw [HyperEnv.Perm_singleton_singleton]
                  exact hPE1.symm
              exact HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this.symm)
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · exact hℋ.trans HyperEnv.Perm.merge_comm
            · rw [HyperEnv.Perm_singleton_singleton]
              rw [← List.cons_append]
              have hP1 : Γ'' ++ w ∶ A :: Γᵣ ~ Γ' ++ w ∶ A :: Γᵣ := by
                apply List.Perm.append
                · exact hPΓ''
                · rfl
              have hP3 : Γ'' ++ Δ'' ~ Γ'' ++ w ∶ A :: Γᵣ := by
                apply List.Perm.append
                · rfl
                · exact hPΔ''
              rw [List.cons_append]
              exact (hP3.trans hP1).trans List.perm_middle
          · exfalso
            have h_post_subst2 : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] := by
              have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                  (HyperEnv.Perm_singleton_singleton.mpr hPE1)
              exact h_post_no_u.trans this
            have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := HyperEnv.Perm_merge_cancel_right h_post_subst2
            have hwin: w ∶ A :: Γ ∈ 𝒢 |ₕ [w ∶ A :: Γ] := by simp
            obtain ⟨E, hE, hPEw⟩ := HyperEnv.Perm_mem hℋ hwin
            have hvEw : v ∶ Cᗮ ∈ w ∶ A :: Γ := List.mem_cons_of_mem _ hΓ
            have hvE := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEw).mpr hvEw
            exact hFv' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ hvE))
      · obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (v, Cᗮ) :: Δᵣ := Env.exists_perm_cons hΔ
        have hPΞ : Ξ ~ Γ‚ Δᵣ := by
          have h1 := hPE_no_x.trans (List.Perm.append_left Γ hPΔ)
          exact List.Perm.cons_inv (h1.trans List.perm_middle)
        refine ⟨𝒢, Γ, (Γ'‚ Δᵣ), ?_, ?_⟩
        · apply HyperEnv.Perm.merge
          · rfl
          · apply HyperEnv.Perm_singleton_singleton.mpr
            have hP1 : x ∶ A ⨂ B :: (Γ'‚ Γ)‚ Δᵣ ~ x ∶ A ⨂ B :: Γ'‚ (Γ‚ Δᵣ) := by
              apply List.Perm.cons
              rw [Env.merge_assoc]
            have hP2 : x ∶ A ⨂ B :: Γ'‚ (Γ‚ Δᵣ) ~ x ∶ A ⨂ B :: Γ'‚ Ξ := by
              apply List.Perm.cons
              apply List.Perm.append
              · rfl
              · exact hPΞ.symm
            have hP3 : x ∶ A ⨂ B :: Γ'‚ Ξ ~ Γ'‚ (x ∶ A ⨂ B :: Ξ) := List.perm_middle.symm
            have hP4 : Γ'‚ (x ∶ A ⨂ B :: Ξ) ~ Γ'‚ Δ' := by
              apply List.Perm.append
              · rfl
              · exact hPΔ'.symm
            have ht : Γ'‚ Δ' ~ x ∶ A ⨂ B :: Γ'‚ Γ‚ Δᵣ :=
              (((hP1.trans hP2).trans hP3).trans hP4).symm
            have hP5 : x ∶ A ⨂ B :: Γ'‚ Γ‚ Δᵣ ~ x ∶ A ⨂ B :: Γ‚ (Γ'‚ Δᵣ) := by
              apply List.Perm.cons
              simp
              apply List.perm_append_comm_assoc
            exact ht.trans hP5
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
              [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.merge_assoc]
            have hP2 : [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] ~
              [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm.cons hPE rfl
            have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
              HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            exact HyperEnv.Perm_merge_cancel_left this
          have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
              (𝒢 |ₕ [u ∶ C :: Γ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
              exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
            exact h_post.trans this
          have hPΓ'' : Γ'' ~ Γ' := by
            have hin : (u ∶ C :: Γ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
            obtain ⟨E, hE, hPEu⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with h | rfl | hwx
            · rcases h with h𝒢 | rfl
              · rcases h𝒢 with h1 | h2
                · exfalso
                  have huA: (u ∶ C) ∈ E := (List.Perm.mem_iff hPEu).mpr (by simp)
                  exact hFu (HyperEnv.subset_names_of_mem h1 (Env.mem_pair_fst_in_names _ huA))
                · rw [h2] at hPEu
                  exact (List.Perm.cons_inv hPEu).symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
                simp at huin
                rcases huin with ⟨rfl, rfl⟩ | huΓ
                · apply huw ; rfl
                · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΓ])
                  simp at huin
                  rcases huin with ⟨rfl, _⟩ | huΞ
                  · apply hneq ; rfl
                  · apply huΔ'
                    apply Env.mem_pair_fst_in_names_iff.mpr
                    use C
                    exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, rfl⟩ | huΔ
              · apply hux ; rfl
              · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΔ])
                simp at huin
                rcases huin with ⟨rfl, _⟩ | huΞ
                · apply hneq ; rfl
                · apply huΔ'
                  apply Env.mem_pair_fst_in_names_iff.mpr
                  use C
                  exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
          have h_post_no_u : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have hPeq : [u ∶ C :: Γ''] ~ [u ∶ C :: Γ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact Env.Perm.cons hPΓ''
            have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ''] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPeq)
                (HyperEnv.Perm.refl _)
            have hP1 := h_post_subst.symm.trans hLHS
            apply HyperEnv.Perm_rotate_rhs_left at hP1
            symm at hP1
            apply HyperEnv.Perm_rotate_rhs_right at hP1
            rw [← HyperEnv.merge_assoc] at hP1
            have hP2 := HyperEnv.Perm_merge_cancel_right hP1
            apply HyperEnv.Perm_rotate_rhs_left at hP2
            symm at hP2
            exact (hP2.trans HyperEnv.Perm.merge_comm).symm
          have ⟨E1, hE1, hPE1⟩ :=
            HyperEnv.Perm_mem (Γ := v ∶ Cᗮ :: Δ'') h_post_no_u.symm (by simp)
          simp at hE1
          rcases hE1 with h𝒢 | rfl | rfl
          · exfalso
            have hvΔ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE1).mpr (by simp)
            exact hFv (HyperEnv.mem_of_mem_mem_names hvΔ h𝒢)
          · exfalso
            have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~ 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Cᗮ :: Δ''] := by
              symm
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm.merge
              · exact HyperEnv.Perm.merge_comm
              · rw [HyperEnv.Perm_singleton_singleton]
                exact hPE1.symm
            have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] :=
              HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this)
            have hxin : x ∶ B :: Δ ∈ 𝒢 |ₕ [x ∶ B :: Δ] := by simp
            obtain ⟨E, hE, hPEx⟩ := HyperEnv.Perm_mem hℋ hxin
            have hvEx : v ∶ Cᗮ ∈ x ∶ B :: Δ := List.mem_cons_of_mem _ hΔ
            have hvE := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEx).mpr hvEx
            exact hFv' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ hvE))
          · have hPΔ'' : Δ'' ~ x ∶ B :: Δᵣ := by
              have h1 := hPE1.symm.trans (List.Perm.cons (x ∶ B) hPΔ)
              have h2 : (x ∶ B :: v ∶ Cᗮ :: Δᵣ) ~ (v ∶ Cᗮ :: x ∶ B :: Δᵣ) := List.Perm.swap ..
              exact List.Perm.cons_inv (h1.trans h2)
            have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := by
              have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] := by
                apply HyperEnv.Perm.merge
                · rfl
                · rw [HyperEnv.Perm_singleton_singleton]
                  exact hPE1
              exact HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this)
            apply HyperEnv.Perm.merge
            · exact hℋ
            · exact HyperEnv.Perm_singleton_singleton.mpr
                ((List.Perm.append hPΓ'' hPΔ'').trans List.perm_middle)

lemma HyperEnv.Perm.extract_parr_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Γ'' Δ' Δ'' : Env} {u v x w : FPName} {A B C : Types}
  (h_pre : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [x ∶ A ⅋ B :: Γ])
  (h_post : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~ 𝒢ᵣ |ₕ [w ∶ A :: x ∶ B :: Γ])
  (hxw : x ≠ w) (hux : u ≠ x) (huw : u ≠ w) (hvx : v ≠ x) (hvw : v ≠ w)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (huΔ' : u ∉ Δ'.names) (hvΓ' : v ∉ Γ'.names) :
  ∃ 𝒢ₙ Γₙ,
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A ⅋ B :: Γₙ] ∧
    ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [w ∶ A :: x ∶ B :: Γₙ] := by
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem (Γ := x ∶ A ⅋ B :: Γ) h_pre (by simp)
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | hh
  · rcases h with hE𝒢 | hEΓ'
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ex : 𝒢 ~ (x ∶ A ⅋ B :: Γ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ'‚ Δ'], Γ, ?_, ?_⟩
      · apply HyperEnv.Perm.trans
        · exact HyperEnv.Perm.merge_right h𝒢Ex [Γ'‚ Δ']
        · have := (HyperEnv.Perm_merge_singleton (x ∶ A ⅋ B :: Γ) (𝒢ᵣ' |ₕ [Γ'‚ Δ'])).symm
          rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
          exact this
      · have h_pre_subst : 𝒢ᵣ |ₕ [x ∶ A ⅋ B :: Γ] ~
          ((x ∶ A ⅋ B :: Γ) :: 𝒢ᵣ') |ₕ ([u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ']) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ex h_pre
          exact this.symm
        rw [← HyperEnv.merge_assoc] at h_pre_subst
        rw [HyperEnv.cons_append (Γ := x ∶ A ⅋ B :: Γ) (𝒢 := 𝒢ᵣ')] at h_pre_subst
        rw [HyperEnv.merge_assoc] at h_pre_subst
        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        simp only [HyperEnv.merge_assoc] at h_post
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post
        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst
        have hvin : v ∶ Cᗮ :: Δ'' ∈ ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by simp
        obtain ⟨Ev, hEv, hPEv⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hvin
        have hyC : (v ∶ Cᗮ) ∈ Ev := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
        have hyinEy : v ∈ Ev.names := Env.mem_pair_fst_in_names _ hyC
        simp only [List.mem_append, List.mem_singleton] at hEv
        rcases hEv with h1 | rfl
        · rcases h1 with h2 | h3
          · rcases h2 with h4 | h5
            · exfalso
              apply hFv
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem h4) hyinEy]
            · subst h5
              simp at hyinEy
              rcases hyinEy with rfl | h6
              · exfalso ; apply hvx ; rfl
              · exfalso
                rcases h6 with rfl | h7
                · exfalso ; apply hvw ; rfl
                · have hΓsub := HyperEnv.mem_names_subset_of_perm_single hE𝒢 hPE
                  exact hFv (hΓsub (Env.mem_pair_fst_in_names_iff.mpr h7))
          · subst h3
            have hin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
            simp at hin
            exfalso
            rcases hin with ⟨rfl, _⟩| h8
            · apply hneq ; rfl
            · exact hvΓ' (Env.mem_pair_fst_in_names _ h8)
        · have h_post' : ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ']) ~
            ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm_merge_cancel_left_inv
            rw [HyperEnv.Perm_singleton_singleton]
            apply List.Perm.cons
            exact List.Perm.cons_inv hPEv
          have h_post_no_v := by
            have ht := h_post_subst.symm.trans h_post'.symm
            simp only [← HyperEnv.merge_assoc] at ht
            apply HyperEnv.Perm_merge_cancel_right at ht
            exact ht
          have huRHS : u ∶ C :: Γ' ∈ 𝒢ᵣ' |ₕ [w ∶ A :: x ∶ B :: Γ] |ₕ [u ∶ C :: Γ'] := by simp
          obtain ⟨Eu, hEuLHS, hPEu⟩ := HyperEnv.Perm_mem h_post_no_v.symm huRHS
          have huinEu : u ∈ Eu.names := by
            have huC: (u ∶ C) ∈ Eu := by
              simp [HasPerm.perm] at hPEu
              have := hPEu.symm.subset
              simp at this
              exact this.1
            exact Env.mem_pair_fst_in_names _ huC
          simp only [List.mem_append, List.mem_singleton] at hEuLHS
          rcases hEuLHS with h9 | h10
          · exfalso ; exact hFu' ((HyperEnv.subset_names_of_mem h9) huinEu)
          · subst h10
            have hPΓ'Γ'' : Γ' ~ Γ'' := List.Perm.cons_inv hPEu.symm
            have hPΔ'Δ'' : Δ' ~ Δ'' := List.Perm.cons_inv hPEv
            have h_post'' : ℋ |ₕ [u ∶ C :: Γ'] ~
              ℋ |ₕ [u ∶ C :: Γ''] := by
              apply HyperEnv.Perm.merge_exchange_right
              exact HyperEnv.Perm_singleton_singleton.mpr hPEu.symm
            have ht := HyperEnv.Perm_merge_cancel_right (h_post''.trans h_post_no_v.symm)
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · exact ht.trans HyperEnv.Perm.merge_comm
            · rw [HyperEnv.Perm_singleton_singleton]
              apply List.Perm.append
              · exact hPΓ'Γ''.symm
              · exact hPΔ'Δ''.symm
    · subst hEΓ'
      have hxin := (List.Perm.mem_iff (a := x ∶ A ⅋ B) hPE).mpr (by simp)
      simp at hxin
      rcases hxin with ⟨rfl, rfl⟩ | h11
      · exfalso ; apply hux ; rfl
      · obtain ⟨Ξ, hPΓ'⟩ : ∃ Ξ, Γ' ~ (x, A ⅋ B) :: Ξ :=
          Env.exists_perm_cons h11
        have hPE_no_x : u ∶ C :: Ξ ~ Γ := by
          have h12 := hPE.symm.trans (List.Perm.cons (u ∶ C) hPΓ')
          have h13 : (u ∶ C :: (x, A ⅋ B) :: Ξ) ~ ((x, A ⅋ B) :: u ∶ C :: Ξ) := List.Perm.swap ..
          exact (h12.trans h13).cons_inv.symm
        have huΓ : (u, C) ∈ Γ := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x ).mp (by simp)
        obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (u, C) :: Γᵣ := Env.exists_perm_cons huΓ
        have hPΞ : Ξ ~ Γᵣ := by exact List.Perm.cons_inv (hPE_no_x.trans hPΓ)
        refine ⟨𝒢, (Γᵣ‚ Δ'), ?_, ?_⟩
        · apply HyperEnv.Perm.merge
          · rfl
          · apply HyperEnv.Perm_singleton_singleton.mpr
            have h14 := List.Perm.append hPΓ' (List.Perm.refl Δ')
            have h15 : ((x, A ⅋ B) :: Ξ)‚ Δ' ~ (x, A ⅋ B) :: (Ξ‚ Δ') := by rfl
            have h16 := List.Perm.cons (x ∶ A ⅋ B) (List.Perm.append hPΞ (List.Perm.refl Δ'))
            exact h14.trans (h15.trans h16)
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
            have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
              [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_comm_assoc
            have hP2 : [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] ~
              [x ∶ A ⅋ B :: Γ] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              apply HyperEnv.Perm.cons
              · have hP3 : (u, C) :: (x, A ⅋ B) :: Ξ ~ (u, C) :: (x, A ⅋ B) :: Γᵣ := by
                  apply List.Perm.cons ; apply List.Perm.cons ; exact hPΞ
                have hP4 : (u, C) :: Γ' ~ (u, C) :: (x, A ⅋ B) :: Ξ := by
                  apply List.Perm.cons ;  exact hPΓ'
                have hP5 :  (x, A ⅋ B) :: (u, C) :: Γᵣ ~ (x, A ⅋ B) :: Γ := by
                  apply List.Perm.cons
                  exact hPΓ.symm
                exact ((hP4.trans hP3).trans (List.Perm.swap ..)).trans hP5
              · rfl
            have hP3 : [x ∶ A ⅋ B :: Γ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⅋ B :: Γ] :=
              HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            exact HyperEnv.Perm_merge_cancel_left this
          have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: x ∶ B :: Γ] := by
            exact h_post.trans (HyperEnv.Perm.merge h𝒢ᵣ (HyperEnv.Perm.refl _))
          have hPΔ'' : Δ'' ~ Δ' := by
            have hin1 : (v ∶ Cᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
            obtain ⟨E, hE, hPEv⟩ := HyperEnv.Perm_mem h_post_subst.symm hin1
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with h17 | rfl
            · rcases h17 with h18 | rfl
              · exfalso
                have hvA: (v ∶ Cᗮ) ∈ E := (List.Perm.mem_iff hPEv).mpr (by simp)
                exact hFv (HyperEnv.subset_names_of_mem h18 (Env.mem_pair_fst_in_names _ hvA))
              · exact (List.Perm.cons_inv hPEv).symm
            · exfalso
              have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
              simp at hvin
              rcases hvin with ⟨rfl, rfl⟩ | hvxΓ
              · apply hvw ; rfl
              · rcases hvxΓ with ⟨rfl, rfl⟩ | hvΓ
                · apply hvx ; rfl
                · have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                    (List.Perm.mem_iff hPE_no_x.symm).mp hvΓ
                  simp at hin2
                  rcases hin2 with ⟨rfl, _⟩ | hvΞ
                  · apply hneq ; rfl
                  · have h3 : (v, Cᗮ) ∈ Γ' :=
                      (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
          have h_post_no_v : ℋ |ₕ [u ∶ C :: Γ''] ~ 𝒢 |ₕ [w ∶ A :: x ∶ B :: Γ] := by
            have : [v ∶ Cᗮ :: Δ''] ~ [v ∶ Cᗮ :: Δ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact Env.Perm.cons hPΔ''
            have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.refl _) this
            have hP1 := hLHS.symm.trans h_post_subst
            have hP2 : 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: x ∶ B :: Γ] ~
              𝒢 |ₕ [w ∶ A :: x ∶ B :: Γ] |ₕ [v ∶ Cᗮ :: Δ'] := by
              simp only [HyperEnv.merge_assoc]
              apply HyperEnv.Perm.merge
              · rfl
              · exact HyperEnv.Perm.merge_comm
            exact HyperEnv.Perm_merge_cancel_right (hP1.trans hP2)
          have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := u ∶ C :: Γ'') h_post_no_v.symm (by simp)
          simp at hE1
          rcases hE1 with h𝒢 | rfl
          · exfalso
            have huΓ := (List.Perm.mem_iff (a := u ∶ C) hPE1).mpr (by simp)
            exact hFu (HyperEnv.mem_of_mem_mem_names huΓ h𝒢)
          · have hPΓ'' : Γ'' ~ w ∶ A :: x ∶ B :: Γᵣ := by
              have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) (List.Perm.cons (x ∶ B) hPΓ))
              have h2 : (w ∶ A :: x ∶ B :: u ∶ C :: Γᵣ) ~ (u ∶ C :: w ∶ A :: x ∶ B :: Γᵣ) := by
                have : w ∶ A :: x ∶ B :: u ∶ C :: Γᵣ ~ w ∶ A :: u ∶ C :: x ∶ B :: Γᵣ := by
                  apply List.Perm.cons
                  apply List.Perm.swap ..
                exact this.trans (List.Perm.swap ..)
              exact List.Perm.cons_inv (h1.trans h2)
            have hℋ : ℋ ~ 𝒢 := by
              have : 𝒢 |ₕ [w ∶ A :: x ∶ B :: Γ] ~ 𝒢 |ₕ [u ∶ C :: Γ''] := by
                apply HyperEnv.Perm.merge (by rfl)
                rw [HyperEnv.Perm_singleton_singleton]
                exact hPE1
              exact HyperEnv.Perm_merge_cancel_right (h_post_no_v.trans this)
            apply HyperEnv.Perm.merge
            · exact hℋ
            · rw [HyperEnv.Perm_singleton_singleton]
              rw [← List.cons_append, ← List.cons_append]
              exact List.Perm.append hPΓ'' hPΔ''
  · subst hh
    have hxin := (List.Perm.mem_iff (a := x ∶ A ⅋ B) hPE).mpr (by simp)
    simp at hxin
    rcases hxin with ⟨rfl, _⟩ | h2
    · exfalso ; apply hvx ; rfl
    · obtain ⟨Ξ, hPΔ'⟩ : ∃ Ξ, Δ' ~ (x, A ⅋ B) :: Ξ := Env.exists_perm_cons h2
      have hPE_no_x : v ∶ Cᗮ :: Ξ ~ Γ := by
        have h1 := hPE.symm.trans (List.Perm.cons (v ∶ Cᗮ) hPΔ')
        have h2 : (v ∶ Cᗮ :: (x, A ⅋ B) :: Ξ) ~ ((x, A ⅋ B) :: v ∶ Cᗮ :: Ξ) := List.Perm.swap ..
        exact (h1.trans h2).cons_inv.symm
      have hvΓ : (v, Cᗮ) ∈ Γ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE_no_x).mp (by simp)
      obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (v, Cᗮ) :: Γᵣ := Env.exists_perm_cons hvΓ
      have hPΞ : Ξ ~ Γᵣ := List.Perm.cons_inv (hPE_no_x.trans hPΓ)
      refine ⟨𝒢, (Γ'‚ Γᵣ), ?_, ?_⟩
      · apply HyperEnv.Perm.merge
        · rfl
        · apply HyperEnv.Perm_singleton_singleton.mpr
          have h1 := List.Perm.append (List.Perm.refl Γ') hPΔ'
          have h2 : Γ'‚ ((x, A ⅋ B) :: Ξ) ~ (x, A ⅋ B) :: Γ'‚ Ξ := List.perm_middle
          have h3 := List.Perm.cons (x ∶ A ⅋ B) (List.Perm.append (List.Perm.refl Γ') hPΞ)
          exact h1.trans (h2.trans h3)
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [u ∶ C :: Γ'] := by
          have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
            [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            apply HyperEnv.Perm_rotate_rhs_left
            rw [HyperEnv.merge_assoc]
          have hP2 : [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] ~
            [x ∶ A ⅋ B :: Γ] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            apply HyperEnv.Perm.cons hPE rfl
          have hP3 : [x ∶ A ⅋ B :: Γ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⅋ B :: Γ] :=
            HyperEnv.Perm.merge_comm
          have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
          exact HyperEnv.Perm_merge_cancel_left this
        have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
          𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [w ∶ A :: x ∶ B :: Γ] := by
          have : 𝒢ᵣ |ₕ [w ∶ A :: x ∶ B :: Γ] ~
            (𝒢 |ₕ [u ∶ C :: Γ']) |ₕ [w ∶ A :: x ∶ B :: Γ] := by
            exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
          exact h_post.trans this
        have hPΓ'' : Γ'' ~ Γ' := by
          have hin : (u ∶ C :: Γ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
          obtain ⟨E, hE, hPEu⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | hwx
          · rcases h with h𝒢 | rfl
            · exfalso
              have huA: (u ∶ C) ∈ E := (List.Perm.mem_iff hPEu).mpr (by simp)
              exact hFu (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ huA))
            · exact (List.Perm.cons_inv hPEu).symm
          · exfalso
            have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
            simp at huin
            rcases huin with ⟨rfl, rfl⟩ | huxΓ
            · apply huw ; rfl
            · rcases huxΓ with ⟨rfl, rfl⟩ | huΓ_f
              · apply hux ; rfl
              · have hin2 : (u, C) ∈ v ∶ Cᗮ :: Ξ := (List.Perm.mem_iff hPE_no_x.symm).mp huΓ_f
                simp at hin2
                rcases hin2 with ⟨rfl, _⟩ | huΞ
                · apply hneq ; rfl
                · have h3 : (u, C) ∈ Δ' := (List.Perm.mem_iff hPΔ').mpr (by simp [huΞ])
                  exact huΔ' (Env.mem_pair_fst_in_names _ h3)
        have h_post_no_u : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~ 𝒢 |ₕ [w ∶ A :: x ∶ B :: Γ] := by
          have hPeq : [u ∶ C :: Γ''] ~ [u ∶ C :: Γ'] := by
            rw [HyperEnv.Perm_singleton_singleton]
            exact Env.Perm.cons hPΓ''
          have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
            ℋ |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ''] := HyperEnv.Perm.merge
              (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPeq)
              (HyperEnv.Perm.refl _)
          have hP1 := hLHS.symm.trans h_post_subst
          apply HyperEnv.Perm_rotate_rhs_left at hP1
          symm at hP1
          apply HyperEnv.Perm_rotate_rhs_left at hP1
          exact (((HyperEnv.Perm_merge_cancel_right hP1).trans
            HyperEnv.Perm.merge_comm).symm).trans HyperEnv.Perm.merge_comm
        have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := v ∶ Cᗮ :: Δ'') h_post_no_u.symm (by simp)
        simp at hE1
        rcases hE1 with h𝒢 | rfl
        · exfalso
          have hvΓ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE1).mpr (by simp)
          exact hFv (HyperEnv.mem_of_mem_mem_names hvΓ h𝒢)
        · have hPΔ'' : Δ'' ~ w ∶ A :: x ∶ B :: Γᵣ := by
            have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) (List.Perm.cons (x ∶ B) hPΓ))
            have h2 : (w ∶ A :: x ∶ B :: v ∶ Cᗮ :: Γᵣ) ~ (v ∶ Cᗮ :: w ∶ A :: x ∶ B :: Γᵣ) := by
              have : w ∶ A :: x ∶ B :: v ∶ Cᗮ :: Γᵣ ~ w ∶ A :: v ∶ Cᗮ :: x ∶ B :: Γᵣ := by
                apply List.Perm.cons
                apply List.Perm.swap ..
              exact this.trans (List.Perm.swap ..)
            exact List.Perm.cons_inv (h1.trans h2)
          have hℋ : ℋ ~ 𝒢 := by
            have : 𝒢 |ₕ [w ∶ A :: x ∶ B :: Γ] ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ''] := by
              apply HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
              rw [HyperEnv.Perm_singleton_singleton]
              exact hPE1
            exact HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this)
          apply HyperEnv.Perm.merge
          · exact hℋ
          · rw [HyperEnv.Perm_singleton_singleton]
            have hP1 : Γ'' ++ Δ'' ~ Δ'' ++ Γ'' := List.perm_append_comm
            have hP2 : Δ'' ++ Γ''  ~ w ∶ A :: x ∶ B :: Γᵣ ++ Γ'' := by
              apply List.Perm.append hPΔ'' (by rfl)
            have hP3 : w ∶ A :: x ∶ B :: Γᵣ ++ Γ'' ~ w ∶ A :: x ∶ B :: Γᵣ ++ Γ' := by
              apply List.Perm.cons
              apply List.Perm.cons
              apply List.Perm.append (by rfl) hPΓ''
            have hP4 : w ∶ A :: x ∶ B :: Γᵣ ++ Γ' ~ w ∶ A :: x ∶ B :: Γ' ++ Γᵣ := by
              apply List.Perm.cons
              apply List.Perm.cons
              apply List.perm_append_comm
            exact ((hP1.trans hP2).trans hP3).trans hP4

set_option maxHeartbeats 300000 in
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




















-- lemma HyperEnv.Perm.extract_res_res
--   {𝒢 ℋ 𝒢ᵣ 𝒢ᵣ' : HyperEnv} {Γ' Γ'' Δ' Δ'' Γ_x Γ_x' Δ_y Δ_y' : Env}
--   {u v x y : FPName} {A C : Types}
--   (h_pre : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
--     𝒢ᵣ |ₕ [x ∶ A :: Γ_x] |ₕ [y ∶ Aᗮ :: Δ_y])
--   (h_post : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
--     𝒢ᵣ' |ₕ [x ∶ A :: Γ_x'] |ₕ [y ∶ Aᗮ :: Δ_y'])
--   (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
--   (hneq_uv : u ≠ v) (hneq_xy : x ≠ y)
--   (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
--   (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
--   (huΔ' : u ∉ Δ'.names) (hvΓ' : v ∉ Γ'.names) :
--   ∃ 𝒢ₙ 𝒢ₙ',
--     𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A :: Γ_x] |ₕ [y ∶ Aᗮ :: Δ_y] ∧
--     ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ' |ₕ [x ∶ A :: Γ_x'] |ₕ [y ∶ Aᗮ :: Δ_y'] := by
--   sorry
