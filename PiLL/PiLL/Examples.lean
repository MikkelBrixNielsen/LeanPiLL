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

/- Some examples of single and multistep transitions -/
example (x : PName) :
  Typing.one (x := x) Typing.mix₀ -[x⟦⟧]->ₜ Typing.mix₀ := by
  apply TypingStep.one

example (x : PName) :
  Typing.one (x := x) Typing.mix₀ -[[x⟦⟧]]->>ₜ Typing.mix₀ := by
  rw [eq_concat_nil]
  apply MTST.stepR
  · apply MTST.refl
  · apply TypingStep.one

example (x y : PName) :
  Typing.bot (x := y) (Typing.one (x := x) Typing.mix₀) -[[y⸨⸩] ∷ₗ x⟦⟧]->>ₜ Typing.mix₀ := by
  apply MTST.stepR
  · rw [eq_concat_nil]
    apply MTST.stepR
    · apply MTST.refl
    · apply TypingStep.bot
  apply TypingStep.one

example (x y : PName) :
  Typing.mix (Typing.one (x := x) Typing.mix₀) (Typing.one (x := y) Typing.mix₀)
  -[(x⟦⟧ |ₗ y⟦⟧)]->ₜ Typing.mix (Typing.mix₀) (Typing.mix₀) := by
  apply TypingStep.syn
  · apply TypingStep.one  -- 𝒟 -[l]-> 𝒟'
  · apply TypingStep.one  -- ℰ -[l']-> ℰ'
  · simp                  -- i(l | l') ∩ f(P | Q) = ∅
  · apply Typing.mix₀     -- 𝒟':= ⊢ 𝟘 ∷ ∅
  · apply Typing.mix₀     -- ℰ':= ⊢ 𝟘 ∷ ∅


/- Small alpha equivalence example -/
def P : Proc := .parr 1 2 (.tensor 2 4 .nil)
def Q : Proc := .parr 1 3 (.tensor 3 4 .nil)

def w := freshName (P.names ∪ Q.names) -- w = 5
def P' :=  renameBound 2 w P --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))
def Q' :=  renameBound 3 w Q --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))

#eval P' = Q'

/- Some examples using proc and env -/
def t := Typing.mix
        (Typing.one (x := 1) (Typing.mix₀))
        (Typing.bot (x := 2) (Typing.one (x := 3) (Typing.mix₀)))

#check t

#eval proc t
-- #eval env t -- Doesn't currenly work do to non-computability of toList on Finset

def 𝒟' := (Typing.one (x := 1) (Typing.mix₀))
def ℱ' := (Typing.bot (x := 2) (Typing.one (x := 3) (Typing.mix₀)))

def p := Typing.mix 𝒟' ℱ'

#eval proc p

variable (P : Proc) (T : HyperEnv)
  (𝒟 : ⊢ 1⟦⟧.𝟘 ∷ ⦃1 ∶ 𝟙⦄) (ℱ : ⊢ 2⸨⸩.3⟦⟧.𝟘 ∷ ⦃2 ∶ ⊥‚ 3 ∶ 𝟙⦄)

-- Does not work when premises aren't concrete proofs
-- def q := Typing.mix 𝒟 ℱ
-- #eval proc q

example : proc (Typing.mix 𝒟 ℱ) = 1⟦⟧.𝟘 |ₚ 2⸨⸩.3⟦⟧.𝟘 := by
  simp only [proc]

example (h : ⊢ P ∷ T) : proc h = P := by
  simp [proc]

example (h : ⊢ P ∷ T) : env h = T := by
  simp [env]

def y : ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥} := by
  apply Typing.mix
  · apply Typing.one
    apply Typing.mix₀
  · apply Typing.bot
    apply Typing.one
    apply Typing.mix₀

#eval proc y
-- #eval env y same as above

example (h : ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥}) :
  ⊢ proc h ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥} := by
  simp only [proc]
  exact h

example (h : ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥}) :
  ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ env h := by
  simp only [env]
  exact h

example (h : ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥}) :
  ⊢ proc h ∷ env h := by
  simp only [proc]
  simp only [env]
  exact h






-- Execution of the first parallel component of P in Latch_xyz
example (x x₁ : PName) :
  (x⸨⸩.x₁⟦⟧.𝟘) -[[x⸨⸩] ∷ₗ x₁⟦⟧]->>ₚ (𝟘) := by
  apply MPST.stepR
  · rw [eq_concat_nil]
    apply MPST.stepR
    · apply MPST.refl
    · apply ProcStep.bot
  · apply ProcStep.one

-- Execution of the second parallel component of P in Latch_xyz
example (y y₁ : PName) :
  y⸨⸩.y₁⟦⟧.𝟘 -[[y⸨⸩] ∷ₗ y₁⟦⟧]->>ₚ 𝟘 := by
  apply MPST.stepR
  · rw [eq_concat_nil]
    apply MPST.stepR
    · apply MPST.refl
    · apply ProcStep.bot
  · apply ProcStep.one

-- Execution of the third parallel component of P in Latch_xyz
example (x₂ y₂ z : PName) :
  x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 -[([x₂⸨⸩] ∷ₗ y₂⸨⸩) ∷ₗ z⟦⟧]->>ₚ 𝟘 := by
  apply MPST.stepR
  · apply MPST.stepR
    · rw [eq_concat_nil]
      apply MPST.stepR
      · apply MPST.refl
      · apply ProcStep.bot
    · apply ProcStep.bot
  · apply ProcStep.one

example :
  1⸨⸩.2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 -[(([1⸨⸩] ∷ₗ 3⸨⸩) ∷ₗ 2⟦⟧) ∷ₗ 4⟦⟧]->>ₚ 𝟘 |ₚ 𝟘 := by
  apply MPST.stepR
  · apply MPST.stepR
    · apply MPST.stepR
      · rw [eq_concat_nil]
        apply MPST.stepR
        · apply MPST.refl
        · apply ProcStep.par₁
          · apply ProcStep.bot
          · simp
      · apply ProcStep.par₂
        · apply ProcStep.bot
        · simp
    · apply ProcStep.par₁
      · apply ProcStep.one
      · simp
  · apply ProcStep.par₂
    · apply ProcStep.one
    · simp

example : 1⸨⸩.2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘
  -[((((([1⸨⸩] ∷ₗ 2⟦⟧) ∷ₗ 3⸨⸩) ∷ₗ4⟦⟧) ∷ₗ 5⸨⸩) ∷ₗ 6⸨⸩) ∷ₗ 7⟦⟧]->>ₚ 𝟘 |ₚ 𝟘 |ₚ 𝟘 := by
  repeat constructor
  · rw [eq_concat_nil]
    · apply MPST.stepR
      · apply MPST.refl
      · apply ProcStep.par₁
        · apply ProcStep.bot
        · simp
  · apply ProcStep.par₁
    · apply ProcStep.one
    · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₁
      · apply ProcStep.bot
      · simp
    · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₁
      · apply ProcStep.one
      · simp
    · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₂
      · apply ProcStep.bot
      · simp
    · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₂
      · apply ProcStep.bot
      · simp
    · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₂
      · apply ProcStep.one
      · simp
    · simp

  -- apply MPST.stepR
  -- · apply MPST.stepR
  --   · apply MPST.stepR
  --     · apply MPST.stepR
  --       · apply MPST.stepR
  --         · apply MPST.stepR
  --           · rw [eq_concat_nil]
  --             apply MPST.stepR
  --             · apply MPST.refl
  --             · apply ProcStep.par₁
  --               · apply ProcStep.bot
  --               · simp
  --           · apply ProcStep.par₁
  --             · apply ProcStep.one
  --             · simp
  --         · apply ProcStep.par₂
  --           · apply ProcStep.par₁
  --             · apply ProcStep.bot
  --             · simp
  --           · simp
  --       · apply ProcStep.par₂
  --         · apply ProcStep.par₁
  --           · apply ProcStep.one
  --           · simp
  --         · simp
  --     · apply ProcStep.par₂
  --       · apply ProcStep.par₂
  --         · apply ProcStep.bot
  --         · simp
  --       · simp
  --   · apply ProcStep.par₂
  --     · apply ProcStep.par₂
  --       · apply ProcStep.bot
  --       · simp
  --     · simp
  -- · apply ProcStep.par₂
  --   · apply ProcStep.par₂
  --     · apply ProcStep.one
  --     · simp
  --   · simp



/- Example of Latch_xyz's process execution (Example 3.3 in PDF) -/
-- example (x x₁ x₂ y y₁ y₂ z : PName) :
--   (𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘)
--   -[x⸨⸩]->ₚ
--   (𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘) := by
--   apply ProcStep.tensor_parr



-- individual step x, y, τ, τ execution of latch
example :
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 1⸨⸩.2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘))
  -[1⸨⸩]->ₚ
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘)) := by
  apply ProcStep.res
  · apply ProcStep.res
    · apply ProcStep.par₁
      · apply ProcStep.bot
      · simp
    · simp
  · simp

example :
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘))
  -[3⸨⸩]->ₚ
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 2⟦⟧.𝟘 |ₚ 4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘)) := by
  apply ProcStep.res
  · apply ProcStep.res
    · apply ProcStep.par₂
      · apply ProcStep.par₁
        · apply ProcStep.bot
        · simp
      · simp
    · simp
  · simp

example :
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 2⟦⟧.𝟘 |ₚ 4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘))
  -[τ]->ₚ
  (𝑣⸨4, 6⸩ 𝟘 |ₚ 4⟦⟧.𝟘 |ₚ 6⸨⸩.7⟦⟧.𝟘) := by
  apply ProcStep.one_bot
  apply ProcStep.res
  · apply ProcStep.syn
    · apply ProcStep.one
    · apply ProcStep.par₂
      · apply ProcStep.bot
      · simp
    · simp
  · simp

example :
  (𝑣⸨4, 6⸩ 𝟘 |ₚ 4⟦⟧.𝟘 |ₚ 6⸨⸩.7⟦⟧.𝟘)
  -[τ]->ₚ
  (𝟘 |ₚ 𝟘 |ₚ 7⟦⟧.𝟘) := by
  apply ProcStep.one_bot
  apply ProcStep.par₂
  · apply ProcStep.syn
    · apply ProcStep.one
    · apply ProcStep.bot
    · simp
  · simp

example :
  (𝟘 |ₚ 𝟘 |ₚ 7⟦⟧.𝟘)
  -[7⟦⟧]->ₚ
  (𝟘 |ₚ 𝟘 |ₚ 𝟘) := by
  apply ProcStep.par₂
  · apply ProcStep.par₂
    · apply ProcStep.one
    · simp
  · simp


-- x(), y(), τ, τ multistep execution of latch
example :
  (𝑣⸨2, 5⸩ (𝑣⸨4, 6⸩ 1⸨⸩.2⟦⟧.𝟘 |ₚ 3⸨⸩.4⟦⟧.𝟘 |ₚ 5⸨⸩.6⸨⸩.7⟦⟧.𝟘))
  -[((([1⸨⸩] ∷ₗ 3⸨⸩) ∷ₗ τ) ∷ₗ τ) ∷ₗ 7⟦⟧]->>ₚ
  (𝟘 |ₚ 𝟘 |ₚ 𝟘)  := by
  apply MPST.stepR
  · apply MPST.stepR
    · apply MPST.stepR
      · apply MPST.stepR
        · rw [eq_concat_nil]
          · apply MPST.stepR
            · apply MPST.refl
            · apply ProcStep.res
              · apply ProcStep.res
                · apply ProcStep.par₁
                  · apply ProcStep.bot
                  · simp
                · simp
              · simp
        · apply ProcStep.res
          · apply ProcStep.res
            · apply ProcStep.par₂
              · apply ProcStep.par₁
                · apply ProcStep.bot
                · simp
              · simp
            · simp
          · simp
      · apply ProcStep.one_bot
        apply ProcStep.res
        · apply ProcStep.syn
          · apply ProcStep.one
          · apply ProcStep.par₂
            · apply ProcStep.bot
            · simp
          · simp
        · simp
    · apply ProcStep.one_bot
      apply ProcStep.par₂
      · apply ProcStep.syn
        · apply ProcStep.one
        · apply ProcStep.bot
        · simp
      · simp
  · apply ProcStep.par₂
    · apply ProcStep.par₂
      · apply ProcStep.one
      · simp
    · simp
