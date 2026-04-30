import PiLL.Model.HyperEnvironment.Lemmas.Basic

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
