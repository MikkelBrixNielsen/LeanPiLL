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
