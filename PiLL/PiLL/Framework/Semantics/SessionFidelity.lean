import PiLL.Framework.Semantics.EnvStep
import PiLL.Framework.Semantics.ProcStep








-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr

-- FIXME: Move exchange rules to the bottom of Typing, revise substNames / Types
--        Can probably combine a lot of cases using constructor doing this

-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere
-- FIXME: Check possibility of removing exchange_env typing rule



-- FIXME: Proof showing substitution avoids capture
-- FIXME: Check possibility of no having exchange rules
-- FIXME: Find different syntax for open?

-- FIXME: Proof of HyperEnv.names only having free names
-- FIXME: Proof that HyperEnv.names = Proc.f
-- FIXME: Something regarding Name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }




lemma typing_inv_one {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⟦⟧․P) 𝒢) :
  (𝒢 ~ [[x ∶ 1]]) ∧ Typing n P ∅ := by
  generalize heq : (#x⟦⟧․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨h1, h2⟩ := ih (P := P) (x := x) heq
    constructor
    · have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
      exact HyperEnv.Perm.trans this h1
    · exact h2

  case exchange_hyper hP ih =>
    have ⟨h1, h2⟩ := ih (P := P) (x := x) heq
    constructor
    · exact HyperEnv.Perm.trans hP.symm h1
    · exact h2

  case one hT _ =>
    simp at heq
    constructor
    · simp [heq.1, HasPerm.perm]
    · simp [heq.2]
      exact hT

lemma typing_inv_tensor {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⟦$N⟧․P) 𝒢) :
  ∃ (A B : Types) (Γ Δ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⨂ B :: Γ‚ Δ]) ∧
    (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) := by
  generalize heq : (#x⟦$N⟧․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env 𝒢' _ _ _ _ _ hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT⟩ := ih (P := P) heq
    use A, B, Γ, Δ, L

    constructor
    · have h_cong : Δ :: 𝒢' ~ Γ :: 𝒢' := by sorry






      sorry
    · exact hT

  case exchange_hyper ih =>
    sorry

  case tensor ih =>
    sorry


















-- FIXME: Lemma : n ⊢ P ∷ 𝒢 → (P.f = 𝒢.names)




-- FIXME: Subject reduction / simulation proof
theorem session_fidelity {n : Nat} {P P' : Proc} {𝒢 : HyperEnv} {l : Lbl} :
  Typing n P 𝒢 → ProcStep P l P' →
  ∃ 𝒢', EnvStep 𝒢 l 𝒢' ∧ Typing n P' 𝒢' := by
  intros hT hPS
  induction hPS generalizing n 𝒢

  case one =>
    obtain ⟨hP, 𝒟⟩ := typing_inv_one hT
    use ∅
    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.one
      · exact HyperEnv.Perm.nil
    · exact 𝒟

  case tensor x y hF =>
    obtain ⟨A, B, Γ, Δ, L, hP, 𝒟⟩ := typing_inv_tensor hT
    use ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])

    constructor
    · exact EnvStep.perm hP.symm (EnvStep.tensor hF) (by simp [HasPerm.perm])
    · apply 𝒟 hF















  all_goals sorry
