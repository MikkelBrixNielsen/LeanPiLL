import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Bot_Res

lemma TypingStepₘ_inv_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ ⊥ :: Γᵣ]) ∧ (𝒢' ~ 𝒢ᵣ |ₕ [Γᵣ]) := by
  generalize hl : (x⸨⸩ : Lbl) = l at hStep
  induction hStep <;> try simp only [HasParen.paren, HasBracket.brack, Lbl.act.injEq,
    reduceCtorEq, Act.bot.injEq] at hl
  case bot Γ _ _ _ _ _ =>
    subst hl
    use ∅, Γ
    simp only [HyperEnv.merge_unitL]
    exact ⟨by rfl, by rfl⟩
  case par₁ ih =>
    simp only at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    expose_names
    use 𝒥 |ₕ ℋ, Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right
      exact HyperEnv.Perm_merge_cancel_right_inv (hP1.trans HyperEnv.Perm.merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP2.trans HyperEnv.Perm.merge_comm
  case par₂ ih =>
    simp only at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    expose_names
    use 𝒥 |ₕ 𝒢_1, Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv (hP1.trans HyperEnv.Perm.merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP2.trans HyperEnv.Perm.merge_comm
  case res A _ _ _ 𝒟 𝒟' u v hneq hu hv hu' hv' hlu hlv _ ih =>
    simp only [HasParen.paren] at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    subst hl
    simp only [Finset.union_assoc, Finset.mem_union, not_or, Lbl.f, fNamesAct, Lbl.i, iNamesAct,
      Finset.union_empty, Finset.mem_singleton, ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨_, hu𝒢, _, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, _⟩ := hv
    obtain ⟨_, hu𝒢', _, _⟩ := hu'
    obtain ⟨_, hv𝒢', _, _⟩ := hv'
    exact HyperEnv.Perm.extract_bot_res
      hP1 hP2 hlu.symm hlv.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq huΔ hvΓ
  case perm_hyper hP hP' _ ih =>
    simp only at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    use 𝒥, Γ'
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2
  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp only at ih
    have ⟨𝒥, Ξ, hP1, hP2⟩ := ih hl
    use 𝒥, Ξ
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2
