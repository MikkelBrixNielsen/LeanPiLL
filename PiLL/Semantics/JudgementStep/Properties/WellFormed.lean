import PiLL.Semantics.JudgementStep.Basic

theorem TypingStepₘ.preserves_WF {n n' 𝒢 𝒢' P P'}
  (𝒟 : n ⊢ P ∷ 𝒢) (𝒟' : n' ⊢ P' ∷ 𝒢') (l : Lbl) :
  TypingStepₘ 𝒟 l 𝒟' → l.WF := by
  intro h
  induction h <;> simp_all only [Lbl.WF]
