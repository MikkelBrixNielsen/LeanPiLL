------------------------------------------ TODOs  ------------------------------------------

/- Meeting Topics

# Process Congruence
  · The definition
  · Exclusion of 𝑣xy π.P ∼ π.𝑣xy P and 𝑣xy Q ∼ Q, valid? Or disprove them? Or
    (bi)simulation is terms of saturated transitions.
  · The cut_swap case being stuck, issues obtaining derivation having the process typed
    with both the xy and ab sets of environments.

# Preservation Theorem (Transition / Step Proof)
  · Should steps from judgement to judgement be a proof showing if a process can make
    a step then it is also possible for the environment? Or should it be an inductive
    like the Typing, and then have another theorem binding process steps, environments
    steps and the combination together. (Theorem for Proc + Env seems more managable)

# ProcStep and EnvStep
  · Well-formedness: Is it okay to have WF premises in the syn rule? Otherwise, how do
    I avoid this. The current restriction seem too lose to proove WF otherwise.

# Substitution lemmas
  · Name: hFresh and hSafe, valid? Or replace with renaming transitivity?
  · Type: Sorry cases, valid to assume Barendregt's? Or need rename equivalence?

# Typing Induvtive and its Side Conditions
  · Should I keep hFresh, hneq etc., or convert to if there is a clash picking and using a
    fresh name yields an equivalent process, which can be used instead.
-/






/- TODO:
  Fix Env -> HyperEnv coercion and Env.mk / merge + HyperEnv merge syntax binding
  and producing weird results
-/


/- TODO: Make process parallel with 𝟘 act as an abelian monoid under (strong) bisimilarity.
   This might need to be a structural congruence (≡)
    · P |ₚ 𝟘 ∼ P
    · P |ₚ Q ∼  Q |ₚ P
    · P |ₚ (Q |ₚ R) ∼ (P |ₚ Q) |ₚ R

    And for cut when it distributes, provided it does not depend on the restricted endpoints.
    I.e. x,y ∉ fn(Q, π) (where π is some prefix)
    · (𝑣⸨x, y⸩ P) |ₚ Q ∼ 𝑣⸨x, y⸩ (P |ₚ Q)
    · 𝑣⸨x,y⸩ (𝑣⸨x', y'⸩ P) ∼ 𝑣⸨x', y'⸩ (𝑣⸨x,y⸩ P)
    · 𝑣⸨x, y⸩ π.P ∼ π.(𝑣⸨x,y⸩ P)    (NOTE: LHS is ill-typed even if RHS is well-typed)
    · 𝑣⸨x, y⸩ Q ∼ Q                 (NOTE: LHS is ill-typed even if RHS is well-typed)

    · Show simulation thingy
-/

/- TODO:
  · Check correctness of ProcStep and EnvStep
  · Show that for any valid typing if the process can make a step, then the environment can
    also make a step.
-/

-- TODO: Make lean print the notation for the Has_ Type Classes

-- TODO: Fix some processes bindnig weirdly (par, cut, etc.)







--------- Might be doing something different now ---------

/- TODO: Extend TypingStep and fix rules
  · If not remade as theorem instead of actual rules then fix
    · input : Types subst for derivations (𝒟{A // X})
    · axcut : PName subst for derivations (𝒟{x // z})
    · dup₂ : n-expansion rule + sigma substitution (𝒟σ)
    · dispose₂ : Make it an n expansion of the c rule (n >= 0)
  · Remove unnecessary @[simp] tags
-/

/- TODO:
  · Depending on Marcos response define alternate version of c- and w-rule which
    also work on thier dependencies.

  · If not and depending on whether or not the current implementations of rules needing
    to apply a substitution work or not - Make it possible to apply a σ to Env and Proc
    just like a PName.

  · Correct the rules using this as needed.
-/

----------------------------------------------------------



--------- This behaves differently due to de Bruijn  ---------


/- TODO: Check if substitution avoids capture as they are
  · if not:
    · implicitly pick freshname / TVar
      · Probably need AlphaEq to do renaming
      · May need pick fresh function for TVar
  · Make a proof that replacement avoids capture
  · NOTE: Currently baked into Typing rules / theorems due to restrictions, if this had to
    change AlphaEq and De Bruijn indices probably needs to be used.
-/

/- TODO: AlphaEQ
  · Extend to full πLL
  · Transitivity proof -> Equivalence relation
  · Check rules depending on AlphaEq work as expected (Don't get stuck)
  · Check if HyperEnv also needs renaming when Proc is renamed
    · No it doesn't, renaming only affects bound names, environment only contains free names
-/

/- TODO:
  · Finish type substitution theorem on judgements.
    · Currently works modulo not prooving it handles renaming correctly
    · If possible get it to work without assuming Barendregt's variable convetion
  · Remove hFresh and hSafe from name substitution proof and use aplha equivalence
    to show it is possible to pick a freshname and get an equivalent process
-/

--------------------------------------------------------------






/- TODO: show erasure for processes and environments / hyperenvironments
  · if 𝒟 -[l]-> 𝒟' then proc(𝒟) -[l]-> proc(𝒟'), and

  · if proc(𝒟) -[l]-> proc(𝒟') then 𝒟 -[l]-> 𝒟' for som proc(𝒟') = P'
    This has some relation to question (3)

  · maybe also prop 3.4 if P -[l]-> P', then i(l) ∩ f(P) = ∅ and,
    when P is well typed i(l) = f(P') \ f(P)

  · Do the above for HyperEnvs as well

  · Both of the above are related to question (4)
-/







/- TODO: Create examples / test usage of:
  · ProcStep
  · EnvStep
  · Typing
  · TypingStep
  · Create replacement examples
-/

/- TODO:
  · Make notation check section in Examples.lean for Proc, Types, Labels and check
    if it works as expected
  · Ensure precedence works as intended
-/

-- TODO: Create some examples for generic µ label thing

-- TODO: Create some examples as well)

-- TODO: Create the qunatifier example Marco gave in discord

-- TODO: Create examples for ?? and !!

-- TODO: Example 5.1 (check if it is compileable)



-- TODO: τ-reflexicity

-- TODO: Look through old revisions of main.pdf and transfer / check marked uncertanties

-- TODO: Maybe add implicit import in relevant files

-- TODO: Fix #eval env (Typing 𝒢 P) not working

-- TODO: Try once more to get binders to bind tighter than infix operators without "()"

-- TODO: Remove unused lemmas

-- TODO: Ensure consistency in using {} and for lemma and theorem arguments use () for
--       associativity, commutivity etc

/- TODO: Look over the proof for judgement name replacement
  · Shorten it if possible
  · Check whether hFresh is needed the in definiton or if the ones from the Typing
    rule are enough
  · Probably ask about whether the current version is fine or if it is too cluttered
-/

/- TODO:
  WF for _Step without having WF hyp in .syn rule. Side condition seems to weak, so
  maybe try and define the size of a label and do induction on the size instead.
-/

/- TODO: Make polymorphic classes for notation s.t.
  · Env / HyperEnv lookup     -- If lookup is computable, use HasParen for notation
  · Check if possible for ⟷  -- stick with subscripts
-/

--------------------------------------- QUESTIONS ---------------------------------------
/-
  Ask about the two unsolved cases in Typing.subst_types, should I keep them as sorry,
  or can I simply restrict substitution to only handle closed types, or should I
  implement alpha equivalence and use that to solve the cases.
-/

/-
  Ask about whether I should keep TypingStep as its own inductive definiton, or
  if it should use ProcStep and EnvStep and just become a Theorem stating the
  validity of derivation after having done a step.
-/

/-
  Is it the typing rules which ensure that a single name cannot be used by multiple
  environments otherwise how is 𝒢(x) supposed to be defined and is it correctly
  understood that typing rules ensure name linearity in environments.
-/

/-
  Get clerafication on whether or not having a HyperEnv defined as Finset (Finset (PNames × Types))
  is okay, since it yields a structure where individually merged envs cannot be distinguished i.e.
  Γ = Γ1, Γ2, but given Γ you cannot get Γ1 and Γ2 from Γ, since Envs don't carry names. Similarly,
  HyperEnvs don't carry names, so when they are merged they exhibit the same behaviour. Thus, the
  internal structure of a HyperEnv is not a flat list like structure of (x, A) pairs but rather
  a it contains Envs which then contain the (x, A) pairs.
-/

--------------------------- Kinda related ---------------------------

/-
  Currently have an issue environments not matching what is required by rules
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

-- (*)
example (y y' z : PName) : ⊢ y'⸨y⸩.z⸨⸩.y'⸨⸩.y⟦⟧.𝟘 ∷ {z ∶ ⊥‚ y' ∶ 𝟙 ⅋ ⊥} := by
  apply Typing.parr
  rw [Env.merge_assoc, Env.merge_comm]
  apply Typing.bot
  apply Typing.bot
  apply Typing.one
  apply Typing.mix₀

-- (#)
example (y y' z : PName) : ⊢ y⸨y'⸩.z⸨⸩.y'⸨⸩.y⟦⟧.𝟘 ∷ {z ∶ ⊥‚ y ∶ ⊥ ⅋ 𝟙} := by
  apply Typing.parr
  rw [Env.merge_assoc, Env.merge_comm, Env.merge_comm (y' ∶ ⊥) (y ∶ 𝟙)]
  apply Typing.bot
  apply Typing.bot
  apply Typing.one
  apply Typing.mix₀
-/

/-
  There are instance of the cut-rule being used when there isn't three parallel HyperEnvs
  present in the derivation
  · Should there be a cut implicitly adding this s.t. a cut with only two parallel
    HyperEnvs can be done or should one just use rewrites to add the third HyperEnv

  · As a result of the above rule one_bot and tensor_parr don't quite match the
    signature in the paper. They have the occurence of an empty HyperEnv to match
    the cut rule as written in the paper with all three HyperEnvs present. But since
    an arbitrary amount of them can be added or removed is this even an issue?
-/

/-
  Ask about how tensor_parr is defined and if it is possible to not have to do rewrite
  to apply cut on an existing cut, since the rule does not produce the premises in the
  same order which is expected for the next cut.
-/

--------------------------- Kinda related ---------------------------

/-
  Get clerafication on the notion of erasure and the diagram on line 467-472. Should
  I include proofs of this, show the square commuting? Or is it enough to just have
  the proc function produce the process of a given judgement and vice versa for env.
  · Ask about Definition 3.1 482-485 and whether I need to show / prove any of it.
    additionally, ask the same about 478-479.
-/

/-
  Should I try and define the transition system for processes mechanically using proc?
  Or would it be best to define it manually? (Vice versa for env)
  · Additionally, should I be able to define the tripls describing the various lts's
    since they respectively are the least relation closed under their SOS rules?
-/

/-
  Get an explanaiton of Remark 3.6
-/

/-
  Get an explanation of pp. 1:13 (line. 602-623)
-/

/-
  What is going on in chapter 4.1
  · Definition 4.1
  · Last two monoid laws for cut being ill-typed, why?
  · TODO: Saturation line 689-694 (is this the same as τ-flexavility)
  · What is meant by πMLL follows local reasoning
  · Is Theorem 4.5 something is also should construct a proof of?
    and by extension derivations, HyperEnv.
  · TODO: Definition 4.11 i.e. being able to count number of parallel components

  · NOTE: Diamond propery (definition 4.14)
    . Erasure => well-typed processes enjoy diamond property
    · Any process violating diamond property is ill-typed
      · TOOD: Find out if a process can be ill-typed and enjoy diamond property?
    · Diamond property ensures τ transitions does not affect possible interactions
      interactions available before a τ transition are also available after

  · why is 𝒗wx (w().0 | x[].y[].0 | x[].z[].0) ill-typed
    · because the cut between w and x is ambigous.
-/


-------- less pressing --------

/-
  I have been encountering situations where the constructor for a rule describing a step
  between two derivations need a premise to be rewritten to fit the expected type. Specifically
  when cut is involved I often need to incorporate a by block to construct the expected typing /
  hyper-environment resulting from doing the step, since the resulting typing / hyper-environment
  does not match exactly what is expected, but is equivalent and can be obtained through rewrites.

  Would you prefer that I keep the by block in favour of having the rules stated as closely to the
  paper as possible, or should I instead try and eliminate the use of by block by making the constructor
  require that the premise is given as closely to the expected form as possible and leave more of the
  rewriting to the user?
-/
