import PiLL.Definitions

---------------------------------------- EXAMPLES ----------------------------------------

-- Latch_xyz example from main.pdf
-- TODO: Try and use simp more, try and omit giving explicit types to cut,
--       in general try minimizing things given to cut
example (x x₁ x₂ y y₁ y₂ z : PName) :
  ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
    x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙 := by
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

-- Example 2.5/ fig 3 from the main.pdf
theorem ℱ (Δ : Env) (R : Proc) (y y' z : PName) (A B : Types)
  (ℱ' : ⊢ R ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) :
  ⊢ y⸨y'⸩.z⸨⸩.R ∷ Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥ := by
  apply Typing.bot _ _ z at ℱ'
  rw [Env.merge_swap_last] at ℱ'
  apply Typing.parr at ℱ'
  rw [Env.merge_swap_last, Env.merge_assoc] at ℱ'
  exact ℱ'

theorem ℰ (Γ Γ' : Env) (Q : Proc) (x x' : PName) (A B : Types)
  (ℰ' : ⊢ Q ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B) :
  ⊢ x⟦x'⟧.Q ∷ Γ‚ Γ'‚ x ∶ A ⊗ B := by
  apply Typing.tensor
  exact ℰ'

theorem 𝒟 (Γ Γ' Δ : Env) (Q R : Proc) (x x' y y' z) (A B : Types)
  (ℰ' : ⊢ Q ∷ Γ‚ x' ∶ A |ₕ Γ'‚ x ∶ B) (ℱ' : ⊢ R ∷ Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) :
  ⊢ 𝑣⸨x, y⸩ x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R ∷ Γ‚ Γ'‚ Δ‚ z ∶ ⊥ := by
    let t := Typing.cut ∅ (Γ‚ Γ') (Δ‚ z ∶ ⊥) (x⟦x'⟧.Q |ₚ y⸨y'⸩.z⸨⸩.R) x y (A ⊗ B)
    repeat rw [HyperEnv.merge_unitL] at t
    conv => lhs ; rhs ; rw [←Env.merge_assoc]
    apply t
    apply Typing.mix
    · conv => lhs ; simp
      apply Typing.tensor
      exact ℰ'
    · apply Typing.bot _ _ z at ℱ'
      rw [Env.merge_swap_last] at ℱ'
      apply Typing.parr at ℱ'
      -- rw [Env.merge_swap_last, Env.merge_assoc] at ℱ'
      -- rw [Env.merge_swap_last, Env.merge_assoc]
      exact ℱ'






example (x : PName) :
  Typing.one 𝟘 x Typing.mix₀ -[x⟦⟧]-> Typing.mix₀ := by
  apply TypingStep.one


-- Doing multiple steps of an execution
-- example (x y : PName) :
--   Typing.bot
--     (x ∶ 𝟙) (x⟦⟧.𝟘) y (Typing.one 𝟘 x Typing.mix₀)
--     -[Lbl.seq (Lbl.act (Act.bot y)) (Lbl.act (Act.one x))]->
--     Typing.mix₀ := by
--   apply TypingSteps.step
--   · apply TypingStep.bot
--   · apply TypingSteps.step
--     · apply TypingStep.one
--     · apply TypingSteps.refl



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






-- Small alpha equivalence example
def P : Proc := .parr 1 2 (.tensor 2 4 .nil)
def Q : Proc := .parr 1 3 (.tensor 3 4 .nil)

def w := freshName (P.names ∪ Q.names)
def P' :=  renameBound 2 w P
def Q':= renameBound 3 w Q
#eval P' = Q'

---------------------------------------- OTHER THINGS ----------------------------------------

-- Lean being able to use comm and assoc when not in an inductive constructor
example (𝒢 : HyperEnv) (Δ Γ Ξ : Env) (x y x' y' : PName) (P' : Proc) (B : Types) :
  Typing ((𝒢 |ₕ {Γ‚ x ∶ B}) |ₕ {Δ‚ Ξ‚ y ∶ Bᗮ}) (𝑣⸨x', y'⸩ P') =
    Typing (𝒢 |ₕ {Γ‚ x ∶ B} |ₕ {(Δ‚ Ξ)‚ y ∶ Bᗮ}) (𝑣⸨x', y'⸩ P') := by simp
