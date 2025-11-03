import PiLL.Definitions

---------------------------------------- EXAMPLES ----------------------------------------

-- Latch_xyz example from main.pdf
-- TODO: Try and use simp more, try and omit giving explicit types to cut,
--       in general try minimizing things given to cut
example (x x₁ x₂ y y₁ y₂ z : PName) :
  ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
    {x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙} := by
  apply Typing.cut ∅ _ _ _ _ _ (𝟙)
  rw [HyperEnv.merge_unitL, Env.merge_comm]
  conv => lhs ; rhs ; rhs ; rw [Env.merge_assoc]
  apply Typing.cut _ _ _ _ _ _ (𝟙)
  apply Typing.mix
  · apply Typing.bot
    apply Typing.one
    exact Typing.mix₀
  · apply Typing.mix
    · rw [Env.merge_comm]
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀
    · conv => lhs ; rhs ; rw [Env.merge_comm, ←Env.merge_assoc] ; lhs ; rw [Env.merge_comm]
      apply Typing.bot
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀

-- Example 2.5/ fig 3 from the main.pdf and some other stuff
theorem ℱ (Δ : Env) (R : Proc) (y y' z : PName) (A B : Types)
  (ℱ' : ⊢ R ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) :
  ⊢ y⸨y'⸩.z⸨⸩.R ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥} := by
  apply Typing.bot at ℱ'
  · rw [Env.merge_swap_last] at ℱ'
    apply Typing.parr at ℱ'
    rw [Env.merge_swap_last, Env.merge_assoc] at ℱ'
    exact ℱ'

theorem ℰ (Γ Γ' : Env) (Q : Proc) (x x' : PName) (A B : Types)
  (ℰ' : ⊢ Q ∷ {Γ‚ x' ∶ A} |ₕ {Γ'‚ x ∶ B}) :
  ⊢ x⟦x'⟧.Q ∷ {Γ‚ Γ'‚ x ∶ A ⊗ B} := by
  apply Typing.tensor
  exact ℰ'

theorem 𝒟 (Γ Γ' Δ : Env) (Q R : Proc) (x x' y y' z) (A B : Types)
  (ℰ' : ⊢ Q ∷ {Γ‚ x' ∶ A} |ₕ {Γ'‚ x ∶ B}) (ℱ' : ⊢ R ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) :
  ⊢ 𝑣⸨x, y⸩ x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R ∷ {Γ‚ Γ'‚ Δ‚ z ∶ ⊥} := by
    let t := Typing.cut ∅ (Γ‚ Γ') (Δ‚ z ∶ ⊥) (x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R) x y (A ⊗ B)
    repeat rw [HyperEnv.merge_unitL] at t
    conv => lhs ; rhs ; rw [←Env.merge_assoc]
    apply t
    apply Typing.mix
    · conv => lhs ; simp
      apply Typing.tensor
      exact ℰ'
    · apply Typing.bot at ℱ'
      · rw [Env.merge_swap_last] at ℱ'
        apply Typing.parr at ℱ'
        -- rw [Env.merge_swap_last, Env.merge_assoc] at ℱ'  -- These would make the goals
        -- rw [Env.merge_swap_last, Env.merge_assoc]        -- look more like in the paper
        exact ℱ'

-- example (Γ Γ' Δ : Env) (x x' y y' z : PName) (A B : Types)
--   (ℰ' : ⊢ 𝟘 ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B) (ℱ' : ⊢ z⸨⸩.𝟘 ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ)
--   (ℰ : ⊢ x⟦x'⟧.𝟘 ∷ Γ‚ Γ'‚ x ∶ A ⊗ B) (ℱ : ⊢ y⸨y'⸩.z⸨⸩.𝟘 ∷ Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥) :
--   Typing.mix ℰ ℱ  -[x⟦x'⟧ |ₗ y⸨y'⸩]-> Typing.mix ℰ' (Typing.bot (x := z) ℱ') := by
--   apply TypingStep.syn
--   · apply TypingStep.tensor
--   · apply TypingStep.parr
--   · simp ; sorry -- TODO: Need disjointness proof x x' y y' being different s.t. ∩ is empty
--   · exact ℰ'     -- how did we do it in Concurrency Theory?
--   · exact ℱ'

-- FIGURE OUT HOW IN THE WORLD I CAN GET LEAN TO LET ME DO RWs ON A GOAL DEFINED FROM HYPOTHESES

-- GET EXECUTION OF 𝒟 TO WORK

/-
            ℰ                                       ℱ
⊢ x⟦x'⟧.Q ∷ Γ‚ Γ'‚ x ∶ A ⊗ B       ⊢ y⸨y'⸩.z⸨⸩.R ∷ Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥
------------------------------------------------------------------------ MIX
  ⊢ x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R ∷ Γ‚ Γ'‚ x ∶ A ⊗ B |ₕ Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ⊥
  ----------------------------------------------------------------- CUT
          ⊢ 𝑣⸨x, y⸩ x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R ∷ Γ‚ Γ'‚ Δ‚ z ∶ ⊥

--[ τ ]->

                                                ℱ'
                                      ⊢ R ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ
          ℰ'                      ---------------------------------- Typing.bot
⊢ Q ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B       ⊢ z⸨⸩.R ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥
-------------------------------------------------------------------- Typing.mix
  ⊢ Q |ₚ z⸨⸩.R ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B |ₕ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥
  ---------------------------------------------------------------- Typing.cut
      ⊢ 𝑣⸨x, y⸩ Q |ₚ z⸨⸩.R ∷ Γ‚ x' ∶ A |ₕ Γ' |ₕ Δ‚ y' ∶ Aᗮ‚ z ∶ ⊥
      -------------------------------------------------------- Typing.cut
          ⊢ 𝑣⸨x', y'⸩ 𝑣⸨x, y⸩ Q |ₚ z⸨⸩.R ∷ Γ |ₕ Γ' |ₕ Δ‚ z ∶ ⊥

--[z⸨⸩]->

          ℰ'                                     ℱ'
⊢ Q ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B             ⊢ R ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ
---------------------------------------------------------------- Typing.mix
  ⊢ Q |ₚ R ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B |ₕ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥
  ------------------------------------------------------------ Typing.cut
      ⊢ 𝑣⸨x, y⸩ Q |ₚ R ∷ Γ‚ x' ∶ A |ₕ Γ' |ₕ Δ‚ y' ∶ Aᗮ‚ z ∶ ⊥
      ----------------------------------------------------- Typing.cut
        ⊢ 𝑣⸨x', y'⸩ 𝑣⸨x, y⸩ Q |ₚ z⸨⸩.R ∷ Γ |ₕ Γ' |ₕ Δ‚ z ∶ ⊥
-/


example (x : PName) :
  Typing.one (x := x) Typing.mix₀ -[x⟦⟧]-> Typing.mix₀ := by
  apply TypingStep.one

example (x : PName) :
  Typing.one (x := x) Typing.mix₀ -[[x⟦⟧]]->> Typing.mix₀ := by
  rw [eq_concat_nil]
  apply MTST.stepR
  · apply MTST.refl
  · apply TypingStep.one

example (x y : PName) :
  Typing.bot (x := y) (Typing.one (x := x) Typing.mix₀) -[[y⸨⸩] ∷ₗ x⟦⟧]->> Typing.mix₀ := by
  apply MTST.stepR
  · rw [eq_concat_nil]
    apply MTST.stepR
    · apply MTST.refl
    · apply TypingStep.bot
  apply TypingStep.one

example (x y : PName) :
  Typing.mix (Typing.one (x := x) Typing.mix₀) (Typing.one (x := y) Typing.mix₀)
  -[(x⟦⟧ |ₗ y⟦⟧)]-> Typing.mix (Typing.mix₀) (Typing.mix₀) := by
  apply TypingStep.syn
  · apply TypingStep.one  -- 𝒟 -[l]-> 𝒟'
  · apply TypingStep.one  -- ℰ -[l']-> ℰ'
  · simp                  -- i(l | l') ∩ f(P | Q) = ∅
  · apply Typing.mix₀     -- 𝒟':= ⊢ 𝟘 ∷ ∅
  · apply Typing.mix₀     -- ℰ':= ⊢ 𝟘 ∷ ∅


-- Small alpha equivalence example
def P : Proc := .parr 1 2 (.tensor 2 4 .nil)
def Q : Proc := .parr 1 3 (.tensor 3 4 .nil)

def w := freshName (P.names ∪ Q.names) -- w = 5
def P' :=  renameBound 2 w P --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))
def Q' :=  renameBound 3 w Q --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))

#eval P' = Q'


/- The issue mentioned on discord -/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})
  (ℱ' : ⊢ P ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) : ℱ -[y⸨y'⸩]-> Typing.bot (x := z) ℱ' := by sorry
  -- change (⊢ y⸨y'⸩.z⸨⸩.P ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥}) at ℱ
  -- subst t
  -- unfold t at ℱ
  -- dsimp [t] at ℱ
  -- rw [← Env.merge_assoc, Env.merge_swap_last] at ℱ  -- creates a copy of ℱ
  -- rw [← Env.merge_assoc, Env.merge_swap_last]    -- motive is not type correct


/- Generally:
  The output from the Typing rules does not play nice with what TypingStep rules expects
  e.g. in example 2.5 in the definition of ℱ applying Typing.bot to ℱ' places z ∶ ⊥ after
  Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ resulting in Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥, which doesn't match what is
  required by TypingStep.parr being (Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ, so having the transition
  ℱ -[y⸨y'⸩]-> Typing.bot (x := z) ℱ' is not currently possible. Unless it somehow is
  possible to do rewrites on Typing.bot (x := z) ℱ' and make it match the premise of
  TypingStep.parr.
-/


example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (t : Env) (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {t})
  (t' : Env) (ℱ' : ⊢ z⸨⸩.P ∷ {t'}) :
  (t = Δ‚ y ∶ Aᗮ ⅋ Bᗮ ‚ z ∶ ⊥) → (t' = Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥) → ℱ -[y⸨y'⸩]-> ℱ' := by
  intro ht ht'
  rw [Env.merge_comm (y ∶ Aᗮ ⅋ Bᗮ) (z ∶ ⊥), ← Env.merge_assoc] at ht
  conv at ht' =>
    rhs ; rhs ; rw [← Env.merge_assoc, Env.merge_comm]
  conv at ht' =>
    rhs ; rw [← Env.merge_assoc]
  subst ht ht'
  apply TypingStep.parr

example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types) (t t' : Env)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {t}) (ℱ' : ⊢ P ∷ {t'}) :
  (t = Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥) → (t' = Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) →
  ℱ -[y⸨y'⸩]-> Typing.bot (x := z) ℱ' := by
  intro ht ht'
  rw [Env.merge_comm (y ∶ Aᗮ ⅋ Bᗮ) (z ∶ ⊥), ← Env.merge_assoc] at ht
  subst ht ht'
  -- cases ℱ
  -- rw [Env.merge_swap_last]
  -- conv => rhs ; rw [Env.merge_swap_last] -- Trying to rewrite ℱ' to match Typingstep.parr rule
  -- apply TypingStep.parr  -- This rule requires that y' ∶ Aᗮ‚ y ∶ Bᗮ is the last part of
  sorry                     -- the HyperEnv but the Typing.bot rule puts z ∶ ⊥ at the end
                            -- of the HyperEnv and I can't rw on Typing.bot (x := z) ℱ'

example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types) (t t' : Env)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {t}) (ℱ' : ⊢ P ∷ {t'}) :
  (t = Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥) → (t' = Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) →
  ℱ -[ [y⸨y'⸩] ∷ₗ z⸨⸩ ]->> ℱ' := by
  intro h1 h2
  rw [Env.merge_comm (y ∶ Aᗮ ⅋ Bᗮ) (z ∶ ⊥), ← Env.merge_assoc] at h1
  subst h1
  apply MTST.stepR
  · rw [eq_concat_nil]
    apply MTST.stepR
    · apply MTST.refl
    · apply TypingStep.parr
  · -- (?𝒟' : ⊢ z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) -[z⸨⸩]-> ℱ'
    -- rw [Env.merge_swap_last] -- need to be able to rewrite in goal but can't?
    -- apply TypingStep.bot
    sorry
  -- wants this z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ} as conclusion here (?)
  sorry

/- Note:
· Writing the terms for a specific env does not result in a type but instead a subtype
  i.e. (t : Δ‚ x ∶ A) yields a subtype so cannot be used like this (ℱ : ⊢ P ∷ t) even
  though this (ℱ : ⊢ P ∷ Δ‚ x ∶ A) is fine. doing this (t := Δ‚ x ∶ A) instead would
  resolve this. But this hides how t looks in the goal and ℱ.
-/

example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (t := Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥) (t' := Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {t}) (ℱ' : ⊢ P ∷ {t'}) :
  ℱ -[y⸨y'⸩]-> ℱ' := by sorry

/- Additionally:
  · It is not possible to do cases on Envs / HyperEnvs since they are Quots
-/


/- Done:
  removed Env -> HyperEnv coercion:
  · Try adding it again when the above issue has been resolved -/
