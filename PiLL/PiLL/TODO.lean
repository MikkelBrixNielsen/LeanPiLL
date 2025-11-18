import PiLL.Definitions
------------------------------------------ TODOs  ------------------------------------------

-- (MAYBE IGNORE SIDE CONDITIONS FOR NOW AND FOCUS ON JUST GETTING THE RULES ETC. TO WORK)

/- TODO: Add side conditions to typing rules enforcing
    · Environments can only contain one occurence of a process name
    · Hyper-environments can only contain one occurence of an environment name
    · i.e. typing rules should enforce linearity
    · Is it perhaps just an assumption that we don't merge Envs / HyperEnvs which
      share a PName or should I add a sidecondition somewhere.
-/

-- TODO: Look at side conditions for transition rules for derivations

/- TODO:
  make Types be non-recursive s.t. tensor A B has A = some atom B = some atom and aren't
  a potential infinite recursion of some other Types.
-/

/- TODO:
  Find out how to define X in Types i.e. the type variable.

  Find out if X in Proc.input is the type variable X in Types or just some instance
  of the Types inductive.

  Should Top and Zero be included????
-/

-- TODO: Check that renaming Types.offer to Types.with does not clash with Leans `with` command?

-- TOOD: Make notation check section in Examples.lean as has been done for Proc's notation

-- TODO: Example 5.1 (check if it is compileable)

-- TODO: Check alpha renaming and extend it to full πLL

/- TODO: Make process parallel with 𝟘 act as an abelian monoid under (strong) bisimilarity
    · P |ₚ 𝟘 ∼ P
    · P |ₚ Q ∼  Q |ₚ P
    · P |ₚ (Q |ₚ R) ∼ (P |ₚ Q) |ₚ R

    And for cut when it distributes, provided it does not depend on the restricted endpoints.
    I.e. x,y ∉ fn(Q, π) (where π is some prefix)
    · (𝑣⸨x, y⸩ P) |ₚ Q ∼ 𝑣⸨x, y⸩ (P |ₚ Q)
    · 𝑣⸨x,y⸩ (𝑣⸨x', y'⸩ P) ∼ 𝑣⸨x', y'⸩ (𝑣⸨x,y⸩ P)
    · 𝑣⸨x, y⸩ π.P ∼ π.(𝑣⸨x,y⸩ P)    (NOTE: LHS is ill-typed even if RHS is well-typed)
    · 𝑣⸨x, y⸩ Q ∼ Q                 (NOTE: LHS is ill-typed even if RHS is well-typed)
-/


/- TODO: show erasure for processes and environments / hyperenvironments
  · if 𝒟 -[l]-> 𝒟' then proc(𝒟) -[l]-> proc(𝒟'), and

  · if proc(𝒟) -[l]-> proc(𝒟') then 𝒟 -[l]-> 𝒟' for som proc(𝒟') = P'
    This has some relation to question (3)

  · maybe also prop 3.4 if P -[l]-> P', then i(l) ∩ f(P) = ∅ and,
    when P is well typed i(l) = f(P') \ f(P)

  · Do the above for HyperEnvs as well

  · Both of the above are related to question (4)
-/

-- τ-reflexicity

-- TODO: Look through old revisions of main.pdf and transfer / check marked uncertanties

-- TODO: Fix #eval env (Typing 𝒢 P) not working

--------------------------------------- QUESTIONS ---------------------------------------
/-
  Is it the typing rules which ensure that a single name cannot be used by multiple
  environments otherwise how is 𝒢(x) supposed to be defined and is it correctly '
  understood that typing rules ensure name linearity in environments.
-/

------------------------------------- Kinda related -------------------------------------

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
-/
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

------------------------------------- Kinda related -------------------------------------

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
  Get some clerafication on how Lbl is defined. Should parallel be recursive on Lbl. Or
  Should it only be defined on single instances of Act. And how is this reflected in
  the transitions rules whihc use parallel labels e.g. for syn should l in P -[l]-> P'
  be able to be a parallel label in itself or should this only be a single action.
-/

/-
  Don't really understand the conclusions of the RES, 𝟙⊥, and ⊗⅋
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

  · why is 𝒗wx (w().0 | x[].y[].0 | x[].z[].0) ill-typed (becuase the two x's?)

-/
