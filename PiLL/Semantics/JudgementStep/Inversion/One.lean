import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.One_Res

lemma TypingStepₘ_inv_one_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧) 𝒟') :
  ∃ 𝒢ᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]]) ∧ (𝒢' ~ 𝒢ᵣ) := by
  generalize hl : (x⟦⟧ : Lbl) = l at hStep
  induction hStep <;> try simp only [HasBracket.brack, HasParen.paren, Lbl.act.injEq,
    reduceCtorEq, Act.one.injEq] at hl
  case one =>
    subst hl
    use ∅
    rw [HyperEnv.merge_unitL]
    exact ⟨by rfl, by rfl⟩
  case par₁ ih =>
    expose_names
    simp only [HasBracket.brack] at ih
    have ⟨𝒢'', hP1, hP2⟩ := ih hl
    use ℋ |ₕ 𝒢''
    constructor
    · apply HyperEnv.Perm_exchange_lhs HyperEnv.Perm.merge_comm
      rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · apply HyperEnv.Perm.trans HyperEnv.Perm.merge_comm
      exact HyperEnv.Perm_merge_cancel_left_inv hP2
  case par₂ ih =>
    expose_names
    simp only [HasBracket.brack] at ih
    have ⟨ℋ''', hP1, hP2⟩ := ih hl
    use 𝒢_1 |ₕ ℋ'''
    constructor
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · exact HyperEnv.Perm_merge_cancel_left_inv hP2
  case res A _ _ _ 𝒟 _ u v huv hu hv hu' hv' hlu hlv _ ih =>
    simp only [HasBracket.brack] at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    subst hl
    simp only [Finset.union_assoc, Finset.mem_union, not_or, Lbl.f, fNamesAct, Lbl.i,
      iNamesAct, Finset.union_empty, Finset.mem_singleton, ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨_, hu𝒢, huΓ, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, hvΔ⟩ := hv
    exact HyperEnv.Perm.extract_one_res hP1 hP2 hlu.symm hlv.symm hu𝒢 hv𝒢 huv huΔ hvΓ
  case perm_hyper hP hP' _ ih =>
    simp only at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    use 𝒥
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2
  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp only at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    use 𝒥
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2
