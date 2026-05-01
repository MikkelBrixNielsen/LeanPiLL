import PiLL.SessionFidelity.EnvStep
import PiLL.SessionFidelity.Typability

theorem subject_reductionₘ {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
  (𝒟 : Typing n P 𝒢) (hPS : ProcStepₘ P l P') :
  ∃ 𝒢', EnvStepₘ 𝒢 l 𝒢' ∧ (Typing n P' 𝒢') := by
  obtain ⟨𝒢', 𝒟', hTS⟩ := typability_subject_reductionₘ 𝒟 hPS
  have hES := session_fidelity_envₘ hTS
  exact ⟨𝒢', hES, 𝒟'⟩
