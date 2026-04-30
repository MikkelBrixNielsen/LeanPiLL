import PiLL.Model.HyperEnvironment.Lemmas.Basic

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
