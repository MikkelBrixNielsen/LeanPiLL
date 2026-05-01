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




lemma TypingStepₘ_preserves_disjoint_or_merges {n n' : Nat} {P P' : Proc}
  {ℋ ℋ' : HyperEnv} {l : Lbl} {𝒟' : n' ⊢ P' ∷ ℋ'}
  (𝒟 : n ⊢ P ∷ ℋ) (hStep : TypingStepₘ 𝒟 l 𝒟')

  {𝒢 : HyperEnv} {Γ Δ : Env} {A : Types} {x y : FPName}
  (hxl : x ∉ l.f ∪ l.i) (hyl : y ∉ l.f ∪ l.i)
  (hP : ℋ ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) :
  (∃ 𝒢' Γ' Δ', ℋ ~ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) ∨
  (∃ 𝒢' ΓΔ', ℋ ~ 𝒢' |ₕ [x ∶ A :: ΓΔ' ++ [y ∶ Aᗮ]]) := by
  induction hStep generalizing 𝒢 Γ Δ

  case one | bot | tensor | parr =>
    exfalso
    have h_len := HyperEnv.Perm.length_eq hP
    simp only [List.length_singleton, List.length_append] at h_len
    omega

  case par₁ =>




    sorry
  case par₂ => sorry



  case syn => sorry
  case one_bot => sorry
  case tensor_parr => sorry
  case res => sorry
  case perm_env =>




    sorry
  case perm_hyper =>



    sorry

















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
