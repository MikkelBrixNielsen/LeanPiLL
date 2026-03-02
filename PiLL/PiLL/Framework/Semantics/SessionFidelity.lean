import PiLL.Framework.Semantics.EnvStep
import PiLL.Framework.Semantics.ProcStep



-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr


-- FIXME: Proof showing substitution avoids capture
-- FIXME: Check possibility of no having exchange rules
-- FIXME: Find different syntax for open?

-- FIXME: Proof of HyperEnv.names only having free names
-- FIXME: Proof that HyperEnv.names = Proc.f
-- FIXME: Something regarding Name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }




lemma typing_inv_one {n : ℕ} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⟦⟧․P) 𝒢) :
  (𝒢 ~ [[x ∶ 1]]) ∧ Typing n P ∅ := by
  generalize heq : (#x⟦⟧․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ih =>
    have := ih (P := P) (x := x) heq
    simp_all

  case exchange_hyper ih =>
    have := ih (P := P) (x := x)
    simp at this
    simp_all

  case one hT _ =>
    simp at heq
    constructor
    · simp [heq.1]
    · simp [heq.2]
      exact hT





lemma EnvStep_equiv {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
  EnvStep 𝒢 l 𝒢' → (𝒢 ~ ℋ) →
  ∃ ℋ', EnvStep ℋ l ℋ' ∧ (𝒢' ~ ℋ') := by
  intros hE
  induction hE
  case one | bot | selectL | selectR | ampL | ampR =>
    intros h
    simp_all
    subst h
    constructor

  case input X | output X =>
    intros h
    simp_all
    subst h
    constructor
    exact X

  all_goals sorry











-- FIXME: Subject reduction / simulation proof
theorem session_fidelity {n : Nat} {P P' : Proc} {𝒢 : HyperEnv} {l : Lbl} :
  Typing n P 𝒢 → ProcStep P l P' →
  ∃ 𝒢', EnvStep 𝒢 l 𝒢' ∧ Typing n P' 𝒢' := by
  intros hT hPS
  induction hPS generalizing n 𝒢

  case one =>
    obtain ⟨hPerm, 𝒟⟩ := typing_inv_one hT



  all_goals sorry
