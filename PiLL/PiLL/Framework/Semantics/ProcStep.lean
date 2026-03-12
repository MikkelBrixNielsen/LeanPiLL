import PiLL.Framework.Model.Process
import PiLL.Framework.Semantics.Labels

-- Helper for being able to dynamically build a dispose process
def buildDisp (names : List FPName) (x : FPName) : Proc :=
  match names with
  | [] => #x⟦⟧․𝟘
  | z :: zs => #z⟦DISP⟧․(buildDisp zs x)

-- Helpers for being able to dynamically build the duplicate process
def closeAll (P : Proc) (idx : Nat) (names : List FPName) : Proc :=
  match names with
  | [] => P
  | z :: zs => closeAll (P⟪idx | z⟫) (idx + 1) zs

def wrapDup (P : Proc) (names : List FPName) : Proc :=
  match names with
  | [] => P
  | z :: zs => Proc.duplicate #z (wrapDup P zs)

-- NOTE: Names should be (P.f.erase x).toList and P should be based proccess
def buildDup (P : Proc) (names : List FPName) (x : FPName) : Proc :=
  -- use closeAll to replace free names with De Bruijn indices to get duplicate server
  -- x :: names has names reversed to have x be innermost binder (bound 0) and zₙ (bound 1)
  let P' := closeAll (Proc.server #x P) 0 (x :: names.reverse)

  -- Wrap x with tensor, and the rest with duplicate
  wrapDup (#x⟦$N⟧․(P' |ₚ (Proc.server #x P))) names

inductive ProcStep : (P : Proc) → Lbl → (P' : Proc) → Prop where
  | one
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦⟧․P) (x⟦⟧) P

  | tensor
      {P : Proc} {x y : FPName} (hF : y ∉ {x} ∪ P.f) :
      ProcStep (#x⟦$N⟧․P) (x⟦y⟧) P⸨#y⸩

  | bot
      {P : Proc} {x : FPName} :
      ProcStep (#x⸨⸩․P) (x⸨⸩) P

  | parr
      {P : Proc} {x y : FPName} (hF: y ∉ {x} ∪ P.f) :
      ProcStep (#x⸨$N⸩․P) (x⸨y⸩) P⸨#y⸩

  | par₁
      {P P' Q : Proc} {l : Lbl} :
      ProcStep P l P' → l.i ∩ Q.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P' |ₚ Q)

  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStep Q l Q' → l.i ∩ P.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P |ₚ Q')

  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStep P l P' → ProcStep Q l' Q' →
      (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  → (l |ₗ l').WF →
      ---------------------------------------------
      ProcStep (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

-- FIXME: Delete, and make theorem stating AlphaEq is handled by LN
--   | alpha_equiv
--       {P Q Q' : Proc} {l : Lbl} :
--       (P =ₐ Q) → ProcStep Q l Q' →
--       -------------------------------
--       ProcStep P l Q'

-- NOTE: P' defined outside forall → x y cannot be in P'
  | one_bot
      {P P' : Proc} (L : Finset FPName) :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      ProcStep P⸨#x, #y⸩ (x⟦⟧ |ₗ y⸨⸩) P') →
      ----------------------------
      ProcStep (𝑣⸨$N,$N⸩ P) (τ) P'

  | tensor_parr
      {P P' : Proc} {x x' y y' : FPName} {L : Finset FPName} :
      (∀ x ∉ L, ∀ x' ∉ L, ∀ y ∉ L, ∀ y' ∉ L,
      x ≠ x' → x ≠ y → x ≠ y' → y ≠ x' → y ≠ y' → x' ≠ y' →
      ProcStep P⸨#x, #y⸩ (x⟦x'⟧ |ₗ y⸨y'⸩) P'⸨#x, #y⸩⸨#x', #y'⸩) →
      ---------------------------------------------------------
      ProcStep (𝑣⸨$N,$N⸩ P) (τ) (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P'))

/- NOTE: x y are fresh from L, so they avoid l.f and l.i, with L = P.f.
         Thus, x, y ∉ l.f ∪ l.i follows automatically -/
  | res
      {P P' : Proc} {l : Lbl} {L : Finset FPName} :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      ProcStep P⸨#x, #y⸩ l P'⸨#x, #y⸩) →
      -------------------------------------
      ProcStep (𝑣⸨$N,$N⸩ P) (l) (𝑣⸨$N,$N⸩ P')

  | disp₁
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦DISP⟧․P) (x⟦DISP⟧) (#x⸨⸩․P)

  | disp₂
      {P : Proc} {x : FPName} :
      ---------------------------------------------------------------
      ProcStep (!#x․{P}) (x⸨DISP⸩) (buildDisp (P.f.erase x).toList x)

  | dup₁
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦DUP⟧⸨$N⸩․P) (x⟦DUP⟧) ((#x⸨$N⸩․P))

  | dup₂
      {P : Proc} {x : FPName} :
      -----------------------------------------------------------------
      ProcStep (!#x․{P}) (x⸨DUP⸩) (buildDup P ((P.f.erase x).toList) x)

  | use₁
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦USE⟧․P) (x⟦USE⟧) P

  | use₂
      {P : Proc} {x : FPName} :
      ProcStep (!#x․{P}) (x⸨USE⸩) P

  | output
      {P : Proc} {x : FPName} {A : Types} :
      ProcStep (#x⟦A⟧․P) (x⟦A⟧) P

  | input
      {P : Proc} {x : FPName} {A : Types} :
      A.lc 0 →
      ProcStep (#x⸨$T⸩․P) (x⸨A⸩) (P{A // 0})

  | selectL
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦𝐋⟧․P) (x⟦𝐋⟧) P

  | ampL
      {P Q : Proc} {x : FPName} :
      ProcStep (#x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐋⸩) P

  | selectR
      {P : Proc} {x : FPName} :
      ProcStep (#x⟦𝐑⟧․P) (x⟦𝐑⟧) P

  | ampR
      {P Q : Proc} {x : FPName} :
      ProcStep (#x․case{𝐋 : P, 𝐑 : Q}) (x⸨𝐑⸩) Q

  | link₁
      {x y : FPName} :
      ProcStep (#x ⟷ₚ #y) (x ⟷ₗ y) 𝟘

  | link₂
      {x y : FPName} :
      ProcStep (#x ⟷ₚ #y) (y ⟷ₗ x) 𝟘

  | com {P P' : Proc} {μ : Mu} {L : Finset FPName} :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      ProcStep P⸨#x, #y⸩ (x⟦μ⟧ |ₗ y⟦μ⟧) P'⸨#x, #y⸩) →
      ----------------------------------------------
      ProcStep (𝑣⸨$N,$N⸩ P) (τ) (𝑣⸨$N,$N⸩ P')

/- NOTE: y is consumed by link → y = x, and z is being replaced by x, thus
         the process can be opened with x for both y and z -/
  | axcut
      {P P' : Proc} {x : FPName} {L : Finset FPName} :
      (∀ y ∉ L, ∀ z ∉ L, y ≠ z →
      ProcStep P⸨#y, #z⸩ (x ⟷ₗ y) P'⸨#y, #z⸩) →
      -----------------------------------------
      ProcStep (𝑣⸨$N,$N⸩ P) (τ) (P'⸨#x, #x⸩)

-- FIXME: Might need this for symmetry depending on how cogruence works out
--   | axcut₂
--       {P P' : Proc} {x : FPName} {L : Finset FPName} :
--       (∀ y ∉ L, ∀ z ∉ L, y ≠ z →
--       ProcStep P⸨#z, #y⸩ (x ⟷ₗ z) P'⸨#z, #y⸩) →
--       -----------------------------------------
--       ProcStep (𝑣⸨$N,$N⸩ P) (τ) (P'⸨#x, #x⸩)



notation:50 P " -[" l "]->ₚ " P' => ProcStep P l P'

theorem ProcStep.preserves_WF (P P' : Proc) (l : Lbl) :
  ProcStep P l P' → l.WF := by
  intro h
  induction h

  case res L _ ih =>
    obtain ⟨x, hx, y, hy, hneq⟩ := exists_two_fresh L
    exact ih x y hx hy hneq

  all_goals
    simp_all [Lbl.WF]

inductive MPST : (P : Proc) → Lbls → (P' : Proc) → Prop where
  | refl
    {P : Proc} :
    ------------
    MPST P (ε) P

  | stepR {l : Lbl} {ls : Lbls} {P P'' P' : Proc} :
    (MPST P ls P'') → (P'' -[l]->ₚ P') →
    ------------------------------------
          MPST P (ls ∷ₗ l) P'

notation:50 P " -[" ls "]->>ₚ " P' => MPST P ls P'
