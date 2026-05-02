import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic

















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
    simp at h_len hxl
    subst h_len
    rw [HyperEnv.merge_nilL] at hP
    have h_len := List.Perm.length_eq (HyperEnv.Perm_singleton_singleton.mp hP)
    simp at h_len
    subst h_len
    have := HyperEnv.Perm_singleton_singleton.mp hP
    simp [HasPerm.perm] at this
    exfalso ; exact hxl this.1.symm

  case bot =>
    expose_names
    have h_len := HyperEnv.Perm.length_eq hP
    simp at h_len hxl
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
    simp at h_len hxl
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
    simp at h_len hxl
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

  case syn => sorry
  case one_bot => sorry
  case tensor_parr => sorry
  case res => sorry

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
