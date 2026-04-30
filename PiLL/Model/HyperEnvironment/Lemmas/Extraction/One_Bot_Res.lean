import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.One_Res
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Bot_Res

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
