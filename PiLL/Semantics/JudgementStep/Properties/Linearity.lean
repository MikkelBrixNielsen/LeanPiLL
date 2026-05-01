import PiLL.Model.Judgement.Properties.Names
import PiLL.Semantics.JudgementStep.Basic
import PiLL.Semantics.JudgementStep.Properties.Names

lemma TypingStepₘ_par_preserves_disjoint {n : Nat} {Q Q' R : Proc} {𝒥 𝒥' 𝒦 : HyperEnv} {l' : Lbl}
  {hTQ : n ⊢ Q ∷ 𝒥} {hTQ' : n ⊢ Q' ∷ 𝒥'} (hTR : n ⊢ R ∷ 𝒦)
  (hStep : TypingStepₘ hTQ l' hTQ') (hD : 𝒥.disjoint 𝒦) (disj : l'.i ∩ R.f = ∅) :
  𝒥'.disjoint 𝒦 := by
    have hsub := TypingStepₘ_names_bound hStep
    simp only [HyperEnv.disjoint] at hsub hD
    have hnf := Typing_f_eq_names hTR
    have : Disjoint (𝒥.names ∪ l'.i) 𝒦.names := by
      simp only [hnf, Finset.disjoint_union_left, hD, true_and] at disj ⊢
      exact Finset.disjoint_iff_inter_eq_empty.mpr disj
    exact Disjoint.mono_left hsub this

lemma TypingStepₘ_syn_preserves_disjoint {n : Nat} {P P' Q Q' : Proc}
  {𝒥 𝒥' 𝒦 𝒦' : HyperEnv} {l' l'' : Act} {hTP : n ⊢ P ∷ 𝒥} {hTP' : n ⊢ P' ∷ 𝒥'}
  {hTQ : n ⊢ Q ∷ 𝒦} {hTQ' : n ⊢ Q' ∷ 𝒦'} (hStepPP' : TypingStepₘ hTP l' hTP')
  (hStepQQ' : TypingStepₘ hTQ l'' hTQ') (hD : 𝒥.disjoint 𝒦)
  (disj : (l' |ₗ l'').i ∩ (P |ₚ Q).f = ∅) (lwf : (l' |ₗ l'').WF) :
  𝒥'.disjoint 𝒦' := by
  have hsubRR' := TypingStepₘ_names_bound hStepPP'
  have hsubQQ' := TypingStepₘ_names_bound hStepQQ'
  have hlwf := Finset.disjoint_iff_inter_eq_empty.mpr lwf
  have hdisj := Finset.disjoint_iff_inter_eq_empty.mpr disj
  have hnfR := Typing_f_eq_names hTP
  have hnfQ := Typing_f_eq_names hTQ
  simp only [Proc.f_par, Lbl.i_par'] at hdisj
  simp only [hnfR, hnfQ, Finset.disjoint_union_left, Finset.disjoint_union_right] at hdisj
  rcases hdisj with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  apply Disjoint.mono hsubRR' hsubQQ'
  simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
  refine ⟨⟨hD, h3⟩, h2.symm, hlwf⟩
