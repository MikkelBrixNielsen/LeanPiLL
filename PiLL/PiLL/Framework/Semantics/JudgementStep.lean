import PiLL.Framework.Model.Judgement
import PiLL.Framework.Semantics.Labels
import PiLL.Framework.Semantics.ProcStep
import PiLL.Framework.Semantics.EnvStep


lemma Env.merge_eq_singleton_iff {Γ Δ : Env} {x : PName} {A : Types} :
  Γ‚ Δ = x ∶ A ↔ (Γ = x ∶ A ∧ Δ = ∅) ∨ (Γ = ∅ ∧ Δ = x ∶ A) ∨ (Γ = x ∶ A ∧ Δ = x ∶ A) := by
  constructor
  · intro h
    have hΓ : Γ ⊆ x ∶ A := by rw [← h] ; exact Finset.subset_union_left
    have hΔ : Δ ⊆ x ∶ A := by rw [← h] ; exact Finset.subset_union_right
    rw [Env.mk, Finset.subset_singleton_iff] at hΓ hΔ
    rcases hΓ with rfl | rfl <;> rcases hΔ with rfl | rfl <;> simp_all [Env.merge]
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Env.merge]

lemma HyperEnv.merge_eq_singleton_iff {Γ : Env} {𝒢 ℋ : HyperEnv} :
  𝒢 |ₕ ℋ = {Γ} ↔ (𝒢 = Γ ∧ ℋ = ∅) ∨ (𝒢 = ∅ ∧ ℋ = Γ) ∨ (𝒢 = Γ ∧ ℋ = Γ) := by
  constructor
  · intro h
    have h𝒢 : 𝒢 ⊆ Γ := by rw [← h] ; exact Finset.subset_union_left
    have hℋ : ℋ ⊆ Γ := by rw [← h] ; exact Finset.subset_union_right
    rw [Finset.subset_singleton_iff] at h𝒢 hℋ
    rcases h𝒢 with rfl | rfl <;> rcases hℋ with rfl | rfl <;> simp_all
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

lemma EnvStep.no_step_empty {l : Lbl} {𝒢 : HyperEnv} (h : EnvStep ∅ l 𝒢) : False := by
  generalize hℰ : (∅ : HyperEnv) = ℰ at h
  induction h
  all_goals simp only [Env.mk, HyperEnv.merge] at hℰ ; symm at hℰ ; simp_all








lemma EnvStep.one_inv'
  {𝒢 𝒢' : HyperEnv} {x : PName} (h : 𝒢 -[x⟦⟧]->ₑ 𝒢') :
  ∃ ℋ₁ ℋ₂, 𝒢  = ℋ₁ |ₕ {x ∶ 1} |ₕ ℋ₂ ∧ 𝒢' = ℋ₁ |ₕ ℋ₂ := by
  generalize hl : (x⟦⟧ : Lbl) = l at h
  induction h with


  | one =>
      refine ⟨∅, ∅, ?_, ?_⟩ <;> simp_all

  | par₁ _ ih =>
      rename_i ℋ _ _
      specialize ih hl
      rcases ih with ⟨ℋ₁, ℋ₂, _, _⟩
      refine ⟨ℋ₁, ℋ₂ |ₕ ℋ, ?_, ?_⟩ <;> simp_all

  | par₂ _ ih =>
    rename_i 𝒢 _ _ _ _
    specialize ih hl
    rcases ih with ⟨ℋ₁, ℋ₂, h𝒢, h𝒢'⟩
    refine ⟨ℋ₁, ℋ₂ |ₕ 𝒢, ?_, ?_⟩
    · rw [h𝒢, ← HyperEnv.merge_assoc (ℋ₁ |ₕ x ∶ 1) ℋ₂ 𝒢, HyperEnv.merge_comm]
    · rw [h𝒢', ← HyperEnv.merge_assoc ℋ₁ _ _, HyperEnv.merge_comm]

  | res step ih =>
    cases step





    sorry

  | _ => simp_all















-- theorem TypingStep {𝒢 ℋ : HyperEnv} {P Q : Proc} {l : Lbl}
--   (hT : ⊢ P ∷ 𝒢) (hPS : P -[l]->ₚ Q) (hES : 𝒢 -[l]->ₑ ℋ) : ⊢ Q ∷ ℋ := by
--   induction hPS
--   case one x =>
--     cases hT
--     generalize h𝒢 : ({x ∶ 1} : HyperEnv) = 𝒢 at hES
--     cases hES

--     case one.one => simp_all

--     case one.par₁ 𝒟 _ _ _ step =>
--       symm at h𝒢
--       rw [HyperEnv.merge_eq_singleton_iff] at h𝒢
--       rcases h𝒢 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
--       · sorry
--       · exfalso
--         apply EnvStep.no_step_empty step
--       · sorry

--     case one.par₂ => sorry
--     case one.res => sorry






-- -- theorem TypingStep' {𝒢 ℋ : HyperEnv} {P Q : Proc} {L : Lbl}
-- --   (hT : Typing 𝒢 P) (hPS : ProcStep P L Q) (hES : EnvStep 𝒢 L ℋ) :
-- --   Typing ℋ Q := by
-- --   induction hPS
-- --   case one =>
-- --     cases hT
-- --     set e := _
-- --     conv at hES =>
-- --       arg 1
-- --       change e
-- --     generalize h : e = e' at hES
-- --     cases hES
-- --     all_goals
-- --       clear! e
-- --     case one => assumption
-- --     case one.par₁ P' x D G G' H step =>











-- inductive TypingStep : {𝒢 : HyperEnv} → {P : Proc} → Typing 𝒢 P →
--   Lbl → {𝒢' : HyperEnv} → {P' : Proc} → Typing 𝒢' P' → Prop where
--   | one
--       {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ ∅} :
--       TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

--   | tensor
--       {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B} :
--       TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

--   | bot
--       {Γ : Env} {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ Γ} :
--       TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

--   | parr
--       {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A‚ x ∶ B} :
--       TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

  -- | par₁
  --     {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
  --     {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'} {ℰ : ⊢ Q ∷ ℋ}
  --     (h : TypingStep 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
  --     -----------------------------------------------------
  --     TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

--   | par₂
--       {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h : TypingStep ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
--       ----------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

--   | syn
--       {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act}
--       {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'}
--       {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h₁ : TypingStep 𝒟 l 𝒟') (h₂ : TypingStep ℰ l' ℰ')
--       (disj : (l |ₗ l').i ∩ (P |ₚ Q).f = ∅)
--       (WF : (l |ₗ l').WF) : -- FIXME: show TypingStep preserves WF without this
--       ---------------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) (l |ₗ l') (Typing.mix 𝒟' ℰ')

--   | alpha_equiv
--       {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ 𝒢} {ℰ' : ⊢ Q' ∷ 𝒢'}
--       (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
--       -----------------------------------------------
--       TypingStep 𝒟 l ℰ'

--   | one_bot
--       {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
--       {𝒟 : ⊢ P ∷  𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥} {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ}
--       (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
--       -------------------------------------------------------
--       TypingStep (Typing.cut 𝒢 ∅ Γ P x y (1) 𝒟) (τ) 𝒟'

--   | tensor_parr
--       {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ x' ∶ A |ₕ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ}
--       (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
--       ----------------------------------------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 (Γ‚ Δ) Ξ P x y (A ⨂ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ (Δ‚ Ξ) (𝑣⸨x', y'⸩ P') x y B
--           (by
--            let inner := Typing.cut (𝒢 |ₕ {Γ‚ x ∶ B}) Δ (Ξ‚ y ∶ Bᗮ) P' x' y' A 𝒟'
--            rw [← Env.merge_assoc] at inner
--            exact inner
--           )
--         )

--   | res
--       {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
--       {x y : PName} {A : Types} {l : Lbl}
--       {𝒟 : Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P}
--       {𝒟' : Typing (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ) P'}
--       (h : TypingStep 𝒟 l 𝒟') (disj : l.fresh [x, y]) :
--       ----------------------------------------------------------------------------
--       TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')

--   | selectL
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} :
--       TypingStep (Typing.oplus₁ (B := B) 𝒟) (x⟦𝐋⟧) 𝒟

--   | selectR
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.oplus₂ (A := A) 𝒟) (x⟦𝐑⟧) 𝒟

--   | ampL
--       {Γ : Env} {P Q : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {ℰ : ⊢ Q ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.amp 𝒟 ℰ) (x⸨𝐋⸩) 𝒟

--   | ampR
--       {Γ : Env} {P Q : Proc} {x : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {ℰ : ⊢ Q ∷ Γ‚ x ∶ B} :
--       TypingStep (Typing.amp 𝒟 ℰ) (x⸨𝐑⸩) ℰ

--   | selectL_amp
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ A ⊕ B |ₕ Δ‚ y ∶ Aᗮ & Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ} :
--       TypingStep 𝒟 (x⟦𝐋⟧ |ₗ y⸨𝐋⸩) 𝒟' →
--       -------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (A ⊕ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y A 𝒟')

--   | selectR_amp
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ A ⊕ B |ₕ Δ‚ y ∶ Aᗮ & Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ y ∶ Bᗮ} :
--       TypingStep 𝒟 (x⟦𝐑⟧ |ₗ y⸨𝐑⸩) 𝒟' →
--       --------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (A ⊕ B) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y B 𝒟')

--   | output
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B{A // X}} :
--       TypingStep (Typing.exists_ 𝒟) (x⟦A⟧) 𝒟

--   | input -- FIXME: Might need typing subst for judgements, test if current is ok
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ B} {h : X ∉ ft(Γ)}
--       -- TypingStep (Typing.forall_ (X := X) 𝒟 h) (x⸨A⸩:) (𝒟{A // X}) --------------------------------------------------------------------------
--       {𝒟' : ⊢ P{A // X} ∷ Γ‚ x ∶ B{A // X}} :
--       TypingStep (Typing.forall_ (X := X) 𝒟 h) (x⸨A⸩) 𝒟'

--   | input_output
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A B : Types} {X : TVar}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ (∃X․B) |ₕ Δ‚ y ∶ ∀X․Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B{A // X} |ₕ Δ‚ y ∶ Bᗮ{A // X}} :

--       TypingStep 𝒟 (x⟦A⟧ |ₗ y⸨A⸩) 𝒟' →
--       -----------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (∃X․B) 𝒟)
--         (τ)
--         (by
--           rw [Types.subst_dual] at 𝒟'
--           exact Typing.cut 𝒢 Γ Δ P' x y (B{A // X}) 𝒟'
--         )

--   | link₁
--       {x y : PName} {A : Types} :
--       TypingStep (Typing.ax (x := x) (y := y) (A := A)) (x ⟷ₗ y) (Typing.mix₀)

--   | link₂
--       {x y : PName} {A : Types} :
--       TypingStep (Typing.ax (x := x) (y := y) (A := A)) (y ⟷ₗ x) (Typing.mix₀)

--   -- NOTE: Only free names can perform actions => HyperEnv only contains free names
--   -- => Renaming of a bound variable only needs to happen in the process term
--   | axcut -- FIXME: Might need typing subst for judgements, test if current is ok
--       {𝒢 : HyperEnv} {Γ : Env} {P P' : Proc} {x y z : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ x ∶ Aᗮ‚ y ∶ A |ₕ Γ‚ z ∶ Aᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ z ∶ Aᗮ}
--       {𝒟'σ : ⊢ P'{x // z} ∷ 𝒢 |ₕ Γ‚ x ∶ Aᗮ} :
--       TypingStep 𝒟 (x ⟷ₗ y) 𝒟' →
--       -----------------------------------
--       TypingStep
--       (Typing.cut 𝒢 (x ∶ Aᗮ) Γ P y z A 𝒟)
--       (τ)
--       -- (𝒟'{x // z}) --------------------------------------------------------------------------------------------------------------------------
--       (𝒟'σ)

--   | quest
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} :
--       TypingStep (Typing.quest 𝒟) (x⟦USE⟧) 𝒟

--   | bang
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} {h : ?ₑΓ} :
--       TypingStep (Typing.bang 𝒟 h) (x⸨USE⸩) 𝒟

--   | bang_quest
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ} :
--       TypingStep 𝒟 (x⟦USE⟧ |ₗ x⸨USE⸩) 𝒟' →
--       ------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y A 𝒟')

--   | dup₁
--       {Γ : Env} {P : Proc} {x x' : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ ??A‚ x' ∶ ??A} :
--       TypingStep (Typing.c 𝒟) (x⟦DUP⟧) (Typing.parr 𝒟)

--   -- FIXME: Needs sigma to be applicable to Proc and Env
--   -- FIXME: Theorem stating subst preserves serverUsable
--   | dup₂
--       {Γ Γσ : Env} {P Pσ : Proc} {x xσ : PName} {A : Types}
--       {names namesσ: List PName} {σ : Renaming}
--       -- NOTE: All the postfix σ variables are only here until σ can be applied to them
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} (h₁ : ?ₑΓ)
--       {𝒟σ : ⊢ Pσ ∷ Γσ‚ xσ ∶ A} (h₂ : ?ₑΓσ)
--       -- NOTE: Maybe don't need ?Γσ since it only contains a name for each dependency in Γ
--       -- which all get paired of (z, zσ), so ?Γσ is consumed during the repeated application
--       -- of the c-rule but there might still be some non-dependencies in Γ, so we keep it?
--       {𝒟σ' : ⊢ (x⟦xσ⟧․(!xσ․{Pσ} |ₚ !x․{P})).open namesσ σ ∷ Γ‚ x ∶ !!Aᗮ ⨂ !!Aᗮ} :
--       P.f ∩ (P.f.image σ) = ∅ →
--       names = (P.f \ {x}).toList.mergeSort (· ≤ ·) →
--       -------------------------------------------------------------------------
--       TypingStep
--         (Typing.bang 𝒟 h₁)
--         (x⸨DUP⸩)
--         -- (Typing.c_ALT? (Typing.tensor (Typing.mix (Typing.bang 𝒟σ h₂) (Typing.bang 𝒟 h₁)))) ------------------------------------------------
--         (𝒟σ')

--   | bang_c
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ} (h : ?ₑΔ)
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ ??A ⅋ ??A |ₕ Δ‚ y ∶ !!Aᗮ ⨂ !!Aᗮ} :
--       TypingStep 𝒟 (x⟦DUP⟧ |ₗ x⸨DUP⸩) 𝒟' →
--       -------------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y (??A ⅋ ??A) 𝒟')

--   | dispose
--       {Γ : Env} {P : Proc} {x : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ Γ} :
--       TypingStep
--         (Typing.w (x := x) (A := A) 𝒟)
--         (x⟦DISP⟧)
--         (Typing.bot (x := x) 𝒟)

--   | dispose₂ -- FIXME
--       {Γ : Env} {P : Proc} {x x' : PName} {A : Types} {names : List PName}
--       {𝒟 : ⊢ P ∷ Γ‚ x ∶ A} (h : ?ₑΓ)
--       {𝒟' : ⊢ (x⟦⟧․𝟘).close names ∷ Γ‚ x ∶ 1} :
--       (P.f \ {x}).toList.mergeSort (· ≤ ·) = names →
--       -----------------------------------------------
--       TypingStep
--         (Typing.bang 𝒟 h)
--         (x⸨DISP⸩)
--         𝒟'

--   | bang_w
--       {𝒢 : HyperEnv} {Γ Δ : Env} {P P' : Proc} {x y : PName} {A : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ x ∶ ??A |ₕ Δ‚ y ∶ !!Aᗮ} (h : ?ₑΔ)
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ ⊥ |ₕ Δ‚ y ∶ 1} :
--       TypingStep 𝒟 (x⟦DISP⟧ |ₗ x⸨DISP⸩) 𝒟' →
--       --------------------------------------
--       TypingStep
--         (Typing.cut 𝒢 Γ Δ P x y (??A) 𝒟)
--         (τ)
--         (Typing.cut 𝒢 Γ Δ P' x y ⊥ 𝒟')


-- notation:50 𝒟 " -[" l "]->ₜ " 𝒟' => TypingStep 𝒟 l 𝒟'

-- theorem TypingStep.preserves_WF (𝒢 𝒢' : HyperEnv) (P P' : Proc)
--   (𝒟 : ⊢ P ∷ 𝒢) (𝒟' : ⊢ P' ∷ 𝒢') (l : Lbl) :
--   TypingStep 𝒟 l 𝒟' → l.WF := by
--   intro h
--   induction h <;> simp_all [Lbl.WF]


-- -- theorem TypingStep.preserves_serverUsableEnv


-- notation:80 "ε" => (List.nil : Lbls)
-- notation:60 xs " ∷ₗ " x => List.concat (xs : Lbls) (x : Lbl)

-- lemma eq_concat_nil {l} :
--   [l] = (ε ∷ₗ l) := by rfl

-- lemma cons_concat_eq {x xs y} :
--   x :: (xs ∷ₗ y) = x :: (xs ∷ₗ y) := by simp

-- lemma append_concat_eq {xs ys y} :
--   xs ++ (ys ∷ₗ y) = (xs ++ ys) ∷ₗ y := by simp

-- lemma cons_append_assoc {x : Lbl} {xs ys : Lbls} :
--   x :: (xs ++ ys) = (x :: xs) ++ ys := by rfl

-- inductive MTST : {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
--   Typing 𝒢 P → Lbls → Typing 𝒢' P' → Prop where
--   | refl
--     {𝒢 : HyperEnv} {P: Proc} {𝒟 : Typing 𝒢 P} :
--     MTST 𝒟 (ε) 𝒟

--   | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
--     (𝒟  : Typing 𝒢  P) (𝒟' : Typing 𝒢' P') (𝒟'' : Typing 𝒢'' P'') :
--     (MTST 𝒟 ls 𝒟'') → (𝒟'' -[l]->ₜ 𝒟') →
--     -------------------------------------
--           MTST 𝒟 (ls ∷ₗ l) 𝒟'

-- notation:50 𝒟 " -[" ls "]->>ₜ " 𝒟' => MTST 𝒟 ls 𝒟'
