import PiLL.Definitions

---------------------------------------- NOTATION -----------------------------------------

section Notation
variable (x y : PName) (P Q : Proc) (A : Types)

-- set_option pp.notation false
#check x⟦⟧.P
#check x⸨⸩.P
#check x⟦y⟧.P
#check x⸨y⸩.P
#check 𝑣⸨x, y⸩ P

#check x⟦𝐋⟧.P
#check x⟦𝐑⟧.P
#check ⸨x⸩.case⦃𝐋 : P, 𝐑 : Q⦄
#check x⟦A⟧:P
#check x⸨A⸩:P
#check !x.⦃P⦄
#check x⟦USE⟧.P
#check x⟦DUP⟧⸨y⸩.P
#check x⟦DISP⟧.P
#check x⟷y

end Notation

---------------------------------------- EXAMPLES ----------------------------------------

section Latch
-- Latch_xyz example from main.pdf
-- TODO: Try and use simp more, try and omit giving explicit types to cut,
--       in general try minimizing things given to cut
example (x x₁ x₂ y y₁ y₂ z : PName) :
  ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
    {x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙} := by
  rw [Env.merge_assoc]
  apply Typing.cut ∅ _ _ _ _ _ (𝟙)
  rw [HyperEnv.merge_unitL, Env.merge_assoc]
  apply Typing.cut _ _ _ _ _ _ (𝟙)
  rw [HyperEnv.merge_assoc]
  apply Typing.mix
  · rw [Env.merge_comm]
    apply Typing.bot
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

end Latch

section Single_Multi_Step
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

end Single_Multi_Step

section AlphaEq
/- Small alpha equivalence example -/
def P : Proc := .parr 1 2 (.tensor 2 4 .nil)
def Q : Proc := .parr 1 3 (.tensor 3 4 .nil)

def w := freshName (P.names ∪ Q.names) -- w = 5
def P' :=  renameBound 2 w P --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))
def Q' :=  renameBound 3 w Q --> Proc.parr 1 5 (Proc.tensor 5 4 (Proc.nil))

#eval P' = Q'

end AlphaEq

section Proc_Env
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
  (𝒟 : ⊢ 1⟦⟧.𝟘 ∷ 1 ∶ 𝟙) (ℱ : ⊢ 2⸨⸩.3⟦⟧.𝟘 ∷ 2 ∶ ⊥‚ 3 ∶ 𝟙)

-- Does not work when premises aren't concrete proofs
-- def q := Typing.mix 𝒟 ℱ
-- #eval proc q

example : proc (Typing.mix 𝒟 ℱ) = 1⟦⟧.𝟘 |ₚ 2⸨⸩.3⟦⟧.𝟘 := by
  simp only [proc]

example (h : ⊢ P ∷ T) : proc h = P := by
  simp [proc]

example (h : ⊢ P ∷ T) : env h = T := by
  simp [env]

def y_proc : ⊢ 1⟦⟧.𝟘 |ₚ 2⸨⸩.1⟦⟧.𝟘 ∷ {1 ∶ 𝟙} |ₕ {1 ∶ 𝟙‚ 2 ∶ ⊥} := by
  apply Typing.mix
  · apply Typing.one
    apply Typing.mix₀
  · apply Typing.bot
    apply Typing.one
    apply Typing.mix₀

#eval proc y_proc
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

end Proc_Env

section Latch_execution
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

-- individual step x, y, τ, τ, z execution of latch
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

-- x(), y(), τ, τ, z multistep execution of latch
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


def x := 1
def x' := 2
def y := 3
def y' := 4
def z := 5
def S := 𝟘
def R := 𝟘

example (Γ Γ' Δ : Env) (A B : Types)
  (ℰ' : ⊢ S ∷ {Γ'‚ x' ∶ A} |ₕ {Γ‚ x ∶ B}) (ℱ' : ⊢ R ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ})
  (ℰ : ⊢ x⟦x'⟧.S ∷ {Γ'‚ Γ‚ x ∶ A ⊗ B}) (ℱ : ⊢ y⸨y'⸩.z⸨⸩.R ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥}) :
  Typing.mix ℰ ℱ  -[x⟦x'⟧ |ₗ y⸨y'⸩]->ₜ Typing.mix ℰ' (Typing.bot (x := z) ℱ') := by
  apply TypingStep.syn
  · apply TypingStep.tensor
  · rw! [Env.merge_swap_last]
    rw! [Env.merge_move_last_two_left]
    apply TypingStep.parr
  · aesop
  · exact ℰ'
  · exact ℱ
  · apply Typing.bot
    exact ℱ'

end Latch_execution


section example_2_5 -- FIXME: Don't depend on definitions from previous section
-- Example 2.5/ fig 3 from the main.pdf and some other stuff
theorem ℱ (Δ : Env) (R : Proc) (y y' z : PName) (A B : Types)
  (ℱ' : ⊢ R ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) :
  ⊢ y⸨y'⸩.z⸨⸩.R ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥} := by
  rw [Env.merge_swap_last]
  apply Typing.parr
  rw [Env.merge_move_second_two_right]
  apply Typing.bot
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
    rw [← Env.merge_assoc] at t
    apply t
    apply Typing.mix
    · apply Typing.tensor
      exact ℰ'
    · apply Typing.parr
      rw [Env.merge_move_second_two_right]
      apply Typing.bot
      exact ℱ'

-- It is possible to either predefine the derivation on which to cut or to build it
-- from scratch (from scratch is a lot more cluttered)
example (Γ Γ' Δ : Env) (A B : Types)
  (ℰ' : ⊢ S ∷ {Γ'‚ x' ∶ A} |ₕ {Γ‚ x ∶ B}) (ℱ' : ⊢ R ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ})
  (ℰ : ⊢ x⟦x'⟧.S ∷ {Γ'‚ Γ‚ x ∶ A ⊗ B}) (ℱ : ⊢ y⸨y'⸩.z⸨⸩.R ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})
  (mix : ⊢ x⟦x'⟧.S |ₚ y⸨y'⸩.z⸨⸩.R ∷ ({Γ'‚ Γ‚ x ∶ A ⊗ B} |ₕ {Δ‚ z ∶ ⊥‚ y ∶ Aᗮ ⅋ Bᗮ})) :
  -- (by
  --   let mix := Typing.mix ℰ ℱ
  --   rw [← HyperEnv.merge_unitL ({Γ'‚ Γ‚ x ∶ A ⊗ B} |ₕ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})] at mix
  --   rw [← HyperEnv.merge_assoc, Env.merge_swap_last Δ (y ∶ Aᗮ ⅋ Bᗮ) (z ∶ ⊥)] at mix
  --   let cut := Typing.cut ∅ (Γ'‚ Γ) (Δ‚ z ∶ ⊥) (x⟦x'⟧.S |ₚ y⸨y'⸩.z⸨⸩.R) x y (A ⊗ B) mix
  --   exact cut
  -- )
  Typing.cut ∅ (Γ'‚ Γ) (Δ‚ z ∶ ⊥) (x⟦x'⟧.S |ₚ y⸨y'⸩.z⸨⸩.R) x y (A ⊗ B) mix
  -[τ]->ₜ
  Typing.cut ∅ Γ (Γ'‚ Δ‚ z ∶ ⊥) (𝑣⸨x', y'⸩ S |ₚ z⸨⸩.R) x y B (by
    let mix := Typing.mix ℰ' (Typing.bot (x := z) ℱ')
    rw [HyperEnv.merge_comm {Γ'‚ x' ∶ A} {Γ‚ x ∶ B}] at mix
    rw [Env.merge_move_second_two_right] at mix
    let cut := Typing.cut ({Γ‚ x ∶ B}) Γ' (Δ‚ y ∶ Bᗮ‚ z ∶ ⊥) (S |ₚ z⸨⸩.R) x' y' A mix
    rw [← Env.merge_assoc, ← Env.merge_assoc,
      ← HyperEnv.merge_unitL ({Γ‚ x ∶ B} |ₕ {Γ'‚ Δ‚ y ∶ Bᗮ‚ z ∶ ⊥}),
      ← HyperEnv.merge_assoc, Env.merge_swap_last] at cut
    exact cut
  )
  := by
  rw! [Env.merge_comm Γ' Γ]
  rw! [Env.merge_assoc Γ' Δ (z ∶ ⊥)]
  apply TypingStep.tensor_parr
  · apply TypingStep.syn
    · rw! [HyperEnv.merge_unitL]
      rw! [HyperEnv.merge_assoc, HyperEnv.merge_unitL ({Γ‚ x ∶ ?B} |ₕ {Γ'‚ x' ∶ ?A})]
      · rw! [HyperEnv.merge_comm {Γ‚ x ∶ ?B} {Γ'‚ x' ∶ ?A}]
        · rw! [Env.merge_comm Γ Γ']
          exact TypingStep.tensor
        · exact B
        · exact A
    · rw! [Env.merge_swap_last (Δ‚ z ∶ ⊥) (y ∶ Bᗮ) (y' ∶ Aᗮ)]
      apply TypingStep.parr
    · aesop
    · rw [HyperEnv.merge_unitL, Env.merge_comm Γ Γ']
      exact ℰ
    · rw [HyperEnv.merge_unitL, HyperEnv.merge_comm]
      exact ℰ'
    · have f := Typing.bot (x := z) ℱ'
      rw [Env.merge_move_second_two_right, Env.merge_swap_last Δ (y ∶ Bᗮ) (y' ∶ Aᗮ)]
      exact f

end example_2_5

section example_3_12
def x1 := 1
def x₁ := 2
def x₂ := 3
def y1 := 4
def y₁ := 5
def y₂ := 6



/- Proc Execution for latch x⸨⸩ and y⸨⸩-/
example :
  (𝑣⸨x₁, y₁⸩ 𝑣⸨x₂, y₂⸩ x1⸨⸩.x₁⟦⟧.𝟘 |ₚ y1⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘)
  -[x1⸨⸩]->ₚ
  (𝑣⸨x₁, y₁⸩ 𝑣⸨x₂, y₂⸩ x₁⟦⟧.𝟘 |ₚ y1⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘)
  := by
  apply ProcStep.res
  · apply ProcStep.res
    · apply ProcStep.par₁
      · apply ProcStep.bot
      · aesop
    · unfold x1 x₂ y₂
      simp
  · unfold x1 x₁ y₁
    simp

example :
  (𝑣⸨x₁, y₁⸩ 𝑣⸨x₂, y₂⸩ x₁⟦⟧.𝟘 |ₚ y1⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘)
  -[y1⸨⸩]->ₚ
  (𝑣⸨x₁, y₁⸩ 𝑣⸨x₂, y₂⸩ x₁⟦⟧.𝟘 |ₚ y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘)
  := by
  apply ProcStep.res
  · apply ProcStep.res
    · apply ProcStep.par₂
      · apply ProcStep.par₁
        · apply ProcStep.bot
        · simp
      · unfold y1 x₁
        simp
    · unfold y1 x₂ y₂
      simp
  · unfold y1 x₁ y₁
    simp

/- Typing making the same execution -/
example (x y z : PName) :
  x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙 -[x⸨⸩]->ₑ y ∶ ⊥‚ z ∶ 𝟙 := by
  rw [Env.merge_assoc, Env.merge_comm]
  apply EnvStep.bot

example :
  y1 ∶ ⊥‚ z ∶ 𝟙 -[y1⸨⸩]->ₑ z ∶ 𝟙 := by
  rw [Env.merge_comm]
  apply EnvStep.bot

end example_3_12


/- REPLACEMENT SYNTAX EXAMPLES -/

def A := (Types.var 0) ⊕ (Types.atom 2)

def B := Types.atom 1
def C := Types.atom 2

#check A{(B ⊕ C) // 2}
#eval A
#eval A{(B ⊕ C) // 0}
#eval A{(B ⊕ C) // 2}


-- FIXME: Add more examples and do for Proc as well
