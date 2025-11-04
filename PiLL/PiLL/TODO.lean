import PiLL.Definitions
------------------------------------------ TODOs  ------------------------------------------

-- (MAYBE IGNORE SIDE CONDITIONS FOR NOW AND FOCUS ON JUST GETTING THE RULES ETC. TO WORK)

/- TODO: In regard to exampel 2.5 and figure 3
    · Fix the examples broken by Typing refactoring
    · See if it is possible to do the execution of in many single steps ?
    · Look in itc-course how executions are defined
    · Define multistep executions
    · Do the execution of D
-/

-- TODO: Look through old revisions of main.pdf and transfer / check marked uncertanties

/- TODO: define πMLL derivation transition rules - I THINK THIS IS FIXED
    · fix how the types don't match but are generic
    · fix how the one_bot rule does not match signature
-/

/- TODO: Make Lean infer more of the arguments given to cut from the judgements instead
of supplying them -/

-- TODO: Check how typings bind and try and get it to match what the rules expect

-- TODO: Alpha renaming

/- TODO: Make names and typing appear in reverse order to match typing rules
    · i.e. x().z[].0 :: z : one, x : bot
    · Should reduce the amount of rw used
    · This would go against how the rules are defined, so maybe don't do this.
      Also Envs / HyperEnvs are unordered, commutative, associative, etc., so
      they can be rearranged using those lemmas, and that should be fine.
-/

/- TODO: Add side conditions to typing rules enforcing
    · Environments can only contain one occurence of a process name
    · Hyper-environments can only contain one occurence of an environment name
    · i.e. typing rules should enforce linearity
-/

-- TODO: Look at sideconditions for transition rules for derivations



-- TODO: make a smart constructor for hyper-environments for less boiler plate?
-- TODO: define wellformedness for hyper-environments
-- TODO: Check that typing rules work and that syntax binds in the way it should

------------ Questions ------------
-- Is it the typing rules which ensure that a single name cannot be used by multiple environments
-- Otherwise how is 𝒢(x) supposed to be defined
-- Is it correctly understood that typing rules ensure name linearity in environments

/- How should hyperenvs be defined
    · just a bag of envs no structure
    · par constructor to keep track of structure
    · processes have a parallel composition keeping them distinct so shouldn't this also
    · be the case for hyperenvironments
-/

/- In the cut rule for πMLL is the typing correct i.e. 𝒢 | Γ, x : A | Δ, y : ¬A becomes 𝒢 | Γ, Δ
    · i.e. is it correct that after the cut Γ and Δ merges into one environment?
    · Or should they stay parallel when merging into 𝒢 again?
-/



------------ Might be irrelevant ------------
-- TODO: use env_linearity to ensure insertions / appends to an env's data are unique entries
-- TODO: use hyper_linearity to ensure insertions / appends to an hyperenv's data are unique entries


----------------------------------------- NOTES -----------------------------------------
/- Linearity on hypersets should be enforced through typing rules and should make it impossible
    to define multiple instances of the same name across different environments s.t. 𝒢(x) is
   unambigous.
-/

/-
FINSET LINKS:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Filter.html    -- Filter
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Fold.html      -- Fold
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html       -- Maximum / minimum
-/

/- We are only concerned about free nanmes in rules like PAR1
   and not converned about shadowing because:
   · Bound names cannot be seen outside / are private to process
   · Thus would be covered by a tau transition
-/

/- Label parallel can only be composed of things from the action set not recursively
from the label set as well -/

/- There is / was a typo in how \McE and \McF are defined in example 2.5, since applying
    tensor / parr to the premise does not yield the shown goal - the type of x / x' and
    y / y' should be swapped.
    · Fabrizio's response: Rules are correct application is wrong. x' should have type A,
      and x type B. Likewise for y and y'.

    · IMPORTANT FACT: It's very easy to make mistakes like the above, because it's intuitive
      to follow the same order in which names and types are presented. But the rules don't do
      this, becuase intuitively 'B' is the type of the 'continuation', so the rules are right
      but a bit unintuitive to apply.

    · (SIDE NOTE from Fabrizio: this is a great example of why using a proof assistant helps
      avoid mistakes)
-/
--------------------------------------- QUESTIONS ---------------------------------------
/-
(1) Isn't the order y and y' in the last HyperEnv of the tensor_parr rule flipped based
    on what the parr rule requires in its signature i.e.:
    applying parr to y⸨y'⸩.P ∷ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ --> P ∷ Ξ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ, but in the example
    applying parr resutls in the reverse order of y and y': P ∷ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ
    (The typing are however correct)
    -- Yes, it has been fixed now.
-/

/-
(2) Currently have an issue environments not matching what is required by rules
    D' would not be the result of direct rule application but needs rw to exist
    direct rule application would create:
    · Typing.mix₀           => 𝟘 ∷ ∅
    · Typing.one (x := y)   => y⟦⟧.𝟘 ∷ y ∶ 𝟙
    · Typing.bot (x := y')  => y⸨⸩.y⟦⟧.𝟘 ∷ y ∶ 𝟙‚ y' ∶ ⊥
    · Typing.bot (x := z)   => z⸨⸩.y⸨⸩.y⟦⟧.𝟘 ∷ y ∶ 𝟙‚ y' ∶ ⊥‚ z ∶ ⊥
    Cannot apply Typing.parr unless z ∶ ⊥ is moved to the front
    And even then two different outcomes can occur, since no order in Envs / HyperEnvs:
    (*) z⸨⸩.y⸨⸩.y⟦⟧.𝟘 ∷ z ∶ ⊥‚ y ∶ 𝟙‚ y' ∶ ⊥
        Typing.parr   => y'⸨y⸩.z⸨⸩.y⸨⸩.y⟦⟧.𝟘 ∷ z ∶ ⊥‚ y' ∶ 𝟙 ⅋ ⊥
    (#) z⸨⸩.y⸨⸩.y⟦⟧.𝟘 ∷ z ∶ ⊥‚ y' ∶ ⊥‚ y ∶ 𝟙
        Typing.parr   => y⸨y'⸩.z⸨⸩.y⸨⸩.y⟦⟧.𝟘 ∷ z ∶ ⊥‚ y ∶ ⊥ ⅋ 𝟙

    Since Envs and HyperEnvs are unordered should it result in (*) or (#), and how do we
    decide how the Env should be ordered when the rule is applied? Is that just something
    we fix / decide before applying the rule? I.e. depending on what we want to show / prove
    we fix the Envs / HyperEnvs to refelct this?
-/
-- (*)
example (y y' z : PName) : ⊢ y'⸨y⸩.z⸨⸩.y'⸨⸩.y⟦⟧.𝟘 ∷ {z ∶ ⊥‚ y' ∶ 𝟙 ⅋ ⊥} := by
  apply Typing.parr
  rw [Env.merge_comm]
  apply Typing.bot
  apply Typing.bot
  apply Typing.one
  apply Typing.mix₀

-- (#)
example (y y' z : PName) : ⊢ y⸨y'⸩.z⸨⸩.y'⸨⸩.y⟦⟧.𝟘 ∷ {z ∶ ⊥‚ y ∶ ⊥ ⅋ 𝟙} := by
  apply Typing.parr
  rw [Env.merge_comm] ; conv => lhs ; rhs ; lhs ; rw [Env.merge_comm]
  apply Typing.bot
  apply Typing.bot
  apply Typing.one
  apply Typing.mix₀


/- This also means there are restriction as to how typings can be written on a process if
a ceratin derivation is desired with regard to doing transitions between derivations.
Below D has to bind Δ and z ∶ ⊥ together, otherwise the typing woun't match the parr
transition rule. -/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (D : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y ∶ Aᗮ ⅋ Bᗮ})
  (D' : ⊢ z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) :
  D -[y⸨y'⸩]-> D' := by
  apply TypingStep.parr

/- And so I cannot get something like the below to work, which would be what is produced
by the typing rules. If I could apply rewrite that would be a different story. -/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (D : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})
  (D' : ⊢ z⸨⸩.P ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥}) :
  D -[y⸨y'⸩]-> D' := by sorry
  -- apply TypingStep.parr

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
