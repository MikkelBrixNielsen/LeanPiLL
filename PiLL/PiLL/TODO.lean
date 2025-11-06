import PiLL.Definitions
------------------------------------------ TODOs  ------------------------------------------

-- (MAYBE IGNORE SIDE CONDITIONS FOR NOW AND FOCUS ON JUST GETTING THE RULES ETC. TO WORK)

/- TOOD: Check all Typing and TypingStep rules -/


/- TODO: In regard to exampel 2.5 and figure 3
    · Fix the examples broken by Typing refactoring
    · See if it is possible to do the execution of in many single steps ?
    · Look in itc-course how executions are defined
    · Define multistep executions
    · Do the execution of D
-/

-- TODO: Look through old revisions of main.pdf and transfer / check marked uncertanties

/- TODO: Define πMLL derivation transition rules - I THINK THIS IS FIXED
    · fix how the types don't match but are generic
    · fix how the one_bot rule does not match signature
-/

/- TODO: Fix #eval env (Typing 𝒢 P) not working -/

/- TODO: Make Lean infer more of the arguments given to cut from the judgements instead
of supplying them -/

-- TODO: Check how typings bind and try and get it to match what the rules expect

/- TODO: Make names and typing appear in reverse order to match typing rules
    · i.e. x().z[].0 :: z : one, x : bot
    · Should reduce the amount of rw used
    · This would go against how the rules are defined, so maybe don't do this.
      Also Envs / HyperEnvs are unordered, commutative, associative, etc., so
      they can be rearranged using those lemmas, and that should be fine.
-/

/- TODO: Evaluate whether to remake inductive types to use defined notation
   or ensure they use the underlying constructors etc. to keep them unaffected
   by possible notation changes (currently pretty inconsistent use of both).
-/

/- TODO: Add side conditions to typing rules enforcing
    · Environments can only contain one occurence of a process name
    · Hyper-environments can only contain one occurence of an environment name
    · i.e. typing rules should enforce linearity
-/

-- TODO: Alpha renaming

-- TODO: Look at sideconditions for transition rules for derivations

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
(1) Currently have an issue environments not matching what is required by rules
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

/-
(2) Having issues with Typing rules constructing HyperEnvs, which are not ordered
    as other typing rules expects. This can be solved with rewrites. But incorporating
    TypingStep the conclusions produced by Typing rules have HyperEnvs which do not match
    what is required by the conclusion of TypingStep. This should also be fixable with
    rewrites but currently I am having issues using rewrites on a TypingStep goal:

    This also means there are restriction as to how typings can be written on a process if
    a ceratin derivation is desired with regard to doing transitions between derivations.
    Below D has to bind Δ and z ∶ ⊥ together, otherwise the typing woun't match the parr
    transition rule.
-/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (D : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y ∶ Aᗮ ⅋ Bᗮ})
  (D' : ⊢ z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) :
  D -[y⸨y'⸩]->ₜ D' := by
  apply TypingStep.parr

/- And so I cannot get something like the below to work, which would be what is produced
by the typing rules. If I could apply rewrite that would be a different story. -/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (D : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})
  (D' : ⊢ z⸨⸩.P ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥}) :
  D -[y⸨y'⸩]->ₜ D' := by sorry
  -- apply TypingStep.parr

/- The issue mentioned on discord -/
example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y ∶ Aᗮ ⅋ Bᗮ})
  (ℱ' : ⊢ z⸨⸩.P ∷ {(Δ‚ z ∶ ⊥)‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) : ℱ -[y⸨y'⸩]->ₜ ℱ' := by
  apply TypingStep.parr

example (Δ : Env) (P : Proc) (y y' z : PName) (A B : Types)
  (ℱ : ⊢ y⸨y'⸩.z⸨⸩.P ∷ {Δ‚ y ∶ Aᗮ ⅋ Bᗮ‚ z ∶ ⊥})
  (ℱ' : ⊢ P ∷ {Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ}) : ℱ -[y⸨y'⸩]->ₜ Typing.bot (x := z) ℱ' := by sorry
  -- simp only [← Env.merge_assoc, Env.merge_swap_last]
  -- simp only [← Env.merge_assoc, Env.merge_comm]
  -- apply TypingStep.parr


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
  (t = Δ‚ y ∶ Aᗮ ⅋ Bᗮ ‚ z ∶ ⊥) → (t' = Δ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ‚ z ∶ ⊥) → ℱ -[y⸨y'⸩]->ₜ ℱ' := by
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
  ℱ -[y⸨y'⸩]->ₜ Typing.bot (x := z) ℱ' := by
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
  ℱ -[ [y⸨y'⸩] ∷ₗ z⸨⸩ ]->>ₜ ℱ' := by
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
  ℱ -[y⸨y'⸩]->ₜ ℱ' := by sorry

/- Additionally:
  · It is not possible to do cases on Envs / HyperEnvs since they are Quots
-/

/- Done:
  removed Env -> HyperEnv coercion:
  · Try adding it again when the above issue has been resolved
  · If this is added again remove all instances of ⦃⦄ to lift Env to HyperEnv
-/

/-
(3) Get clerafication on the notion of erasure and the diagram on line 467-472. Should
    I include proofs of this, show the square commuting? Or is it enough to just have
    the proc function produce the process of a given judgement and vice versa for env.
-/

/-
(4) Should I try and define the transition system fro processes mechanically using proc?
    Or would it be best to define it manually? (Vice versa for env)
-/

/-
(5) Get some clerafication on how Lbl is defined. Should parallel be recursive on Lbl. Or
    Should it only be defined on single instances of Act. And how is this reflected in
    the transitions rules whihc use parallel labels e.g. for syn should l in P -[l]-> P'
    be able to be a parallel label in itself or should this only be a single action.
-/

/-
(6) Ask about whether the way Proc.par is defined to only use the Proc._par constructor
    when both given processes aren't 𝟘 is valid or if it should be redefined.
-/

/-
(7) With HyperEnvs / Envs not caring about order is there a reason for tensor and parr
    transition rules in Fig. 5 to have the order of x and x' flipped in the HyperEnv
    compared to the other similar rules. The others have them x' then x, but here its
    x then x'.

    NOTE: Depending on the answer to this EnvStep.parr, .tensor, .tensor_parr
          might need to be changed.
-/

/-
(8) Don't really understand the conclusions of the RES, 𝟙⊥, and ⊗⅋
-/
