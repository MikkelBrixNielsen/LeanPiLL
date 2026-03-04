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

-- lemma Typing.f_subset_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   P.f ⊆ 𝒢.names := by
--   induction h



-- lemma Typing.names_subset_f {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   𝒢.names ⊆ P.f := by
--   induction h


@[simp] lemma Env.names_nil :
  Env.names [] = ∅ := by simp [Env.names]

@[simp] lemma Env.names_singleton {x : FPName} {A : Types} :
  Env.names [x ∶ A] = {x} := by simp [Env.names]

@[simp] lemma Env.names_distributes {Γ : Env} {x : FPName} {A : Types} :
  Env.names (x ∶ A :: Γ) = {x} ∪ Γ.names := by simp [Env.names]

@[simp] lemma Env.names_merge {Γ Δ : Env} :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by simp [Env.names]





@[simp] lemma HyperEnv.names_nil :
  HyperEnv.names [] = ∅ := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_singleton (Γ : Env) :
  HyperEnv.names [Γ] = Γ.names := by
  simp [HyperEnv.names, Env.names, List.foldr]

@[simp] lemma HyperEnv.names_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names, Env.names]

@[simp] lemma HyperEnv.names_merge (𝒢 ℋ : HyperEnv) :
  (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  induction 𝒢
  case nil => simp [HyperEnv.names]
  case cons _ _ ih => simp ; rw [ih]







@[simp] lemma Proc.f_one {P : Proc} {u : Channel} :
  (u⟦⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_bot {P : Proc} {u : Channel} :
  (u⸨⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_tensor {P : Proc} {u : Channel} :
  (u⟦$N⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_parr {P : Proc} {u : Channel} :
  (u⸨$N⸩․P).f = u.f ∪ P.f := by simp [Proc.f]



@[simp] lemma Proc.f_open_nil {u : Channel} :
  𝟘⸨u⸩.f = ∅ := by simp [HasOpen.open_, Proc.open, Proc.f]




@[simp] lemma Channel.f_open_erase {k : ℕ} {x : Channel} {y : FPName} (hy : y ∉ x.f) :
  (Channel.open k #y x).f.erase y = x.f := by
  cases x with
  | bound =>
    simp [Channel.open]
    split_ifs <;> simp
  | free z => simp [-Channel.f, Channel.open, hy]




@[simp] lemma Proc.f_open_erase {P : Proc} {y : FPName} (hy : y ∉ P.f) :
  (P⸨#y⸩.f).erase y = P.f := by
  induction P

  case nil => simp [HasOpen.open_, Proc.open, Proc.f]

  case one x _ ih =>
    simp [- channelHasOpen.open_ ]










lemma Typing.f_eq_names {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → P.f = 𝒢.names := by
  intro h
  induction h

  case mix₀ => simp [Proc.f]

  case mix ih1 ih2 =>
    simp [Proc.f]
    rw [ih1, ih2]

  case one ih | bot ih => simp [ih] at ⊢ ih

  case cut => sorry

  case tensor Γ Δ P x _ _ _ _ L _ ih =>
    simp at ⊢ ih
    have ⟨y, hy⟩ := exists_one_fresh (L ∪ Γ.names ∪ Δ.names)
    simp at hy
    have := ih y hy.1








  sorry



-- FIXME: Check that this covers all rules mentioned in the paper
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
