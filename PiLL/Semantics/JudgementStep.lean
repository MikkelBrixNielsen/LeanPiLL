import PiLL.Model.Judgement
import PiLL.Semantics.Labels

-- Same reason as in Environment.lean
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

inductive TypingStepₘ : {n : Nat} → {𝒢 : HyperEnv} → {P : Proc} → Typing n P 𝒢 →
  Lbl → {n' : Nat} → {𝒢' : HyperEnv} → {P' : Proc} → Typing n' P' 𝒢' → Prop where

  | one
      {P : Proc} {x : FPName} {n : Nat} {𝒟 : Typing n P ∅} :
      TypingStepₘ (Typing.one (x := x) 𝒟) (x⟦⟧) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : FPName} {n : Nat} {hF : x ∉ Γ.names}
      {𝒟 : Typing n P [Γ]} :
      TypingStepₘ (Typing.bot (x := x) hF 𝒟) (x⸨⸩) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x y : FPName} {A B : Types} {n : Nat}
      {hF: x ∉ Γ.names ∧ x ∉ Δ.names} {L : Finset FPName} {hy : y ∉ L}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])} :
      TypingStepₘ (Typing.tensor hF L huniq) (x⟦y⟧) (huniq y hy)

  | parr
      {Γ : Env} {P : Proc} {x y : FPName} {A B : Types} {n : Nat}
      {hF : x ∉ Γ.names} {L : Finset FPName} {hy : y ∉ L}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) [z ∶ A :: x ∶ B :: Γ]} :
      TypingStepₘ (Typing.parr hF L huniq) (x⸨y⸩) (huniq y hy)

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢'.disjoint ℋ}
      {𝒟 : Typing n P 𝒢} {𝒟' : Typing n P' 𝒢'} {ℰ : Typing n Q ℋ}
      (h : TypingStepₘ 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) l (Typing.mix hD2 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢.disjoint ℋ'}
      {𝒟 : Typing n P 𝒢} {ℰ : Typing n Q ℋ} {ℰ' : Typing n Q' ℋ'}
      (h : TypingStepₘ ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) l (Typing.mix hD2 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢'.disjoint ℋ'}
      {𝒟 : Typing n P 𝒢} {𝒟' : Typing n P' 𝒢'}
      {ℰ : Typing n Q ℋ} {ℰ' : Typing n Q' ℋ'}
      (h₁ : TypingStepₘ 𝒟 l 𝒟') (h₂ : TypingStepₘ ℰ l' ℰ')
      (disj : (l |ₗ l').i ∩ (P |ₚ Q).f = ∅)
      (WF : (l |ₗ l').WF) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) (l |ₗ l') (Typing.mix hD2 𝒟' ℰ')

  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {P P' : Proc} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
        Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ 1 :: ∅] |ₕ [y ∶ ⊥ :: Γ])}
      {𝒟' : Typing n P' (𝒢 |ₕ [Env.merge ∅ Γ])}
      (h : ∀ x y, (hx : x ∉ L) → (hy : y ∉ L) → (hneq : x ≠ y) →
        TypingStepₘ (huniq x y hx hy hneq) (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {A B : Types} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                Typing n
                  (P⸨#x, #y⸩)
                  (𝒢 |ₕ [x ∶ A ⨂ B :: Env.merge Γ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])}
      {huniq' : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                ∀ x' y', x' ∉ L → y' ∉ L → x' ≠ y' →
                x ≠ x' → x ≠ y' → y ≠ x' → y ≠ y' →
                Typing n
                  (P'⸨#x, #y⸩⸨#x', #y'⸩)
                  (𝒢 |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ])}
      {𝒟' : Typing n (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P')) (𝒢 |ₕ [Env.merge (Env.merge Γ Δ) Ξ])}
      (h : ∀ x y, (hx : x ∉ L) → (hy : y ∉ L) → (hneq : x ≠ y) →
            ∀ x' y', (hx' : x' ∉ L) → (hy' : y' ∉ L) → (hneq' : x' ≠ y') →
              (hxx' : x ≠ x') → (hxy' : x ≠ y') → (hyx' : y ≠ x') → (hyy' : y ≠ y') →
              TypingStepₘ
                (huniq x y hx hy hneq)
                (x⟦x'⟧ |ₗ y⸨y'⸩)
                (huniq' x y hx hy hneq x' y' hx' hy' hneq' hxx' hxy' hyx' hyy')) :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

| res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {A : Types} {n : Nat} {l : Lbl}
      {L : Finset FPName}
      {huniq : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])}
      {huniq' : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                Typing n (P'⸨#x, #y⸩) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'])}
      (h : ∀ x y, (hx : x ∉ L) → (hy : y ∉ L) → (hneq : x ≠ y) →
           TypingStepₘ (huniq x y hx hy hneq) l (huniq' x y hx hy hneq))
      (h_fresh : ∀ x y, x ∉ L → y ∉ L → x ∉ l.f ∪ l.i ∧ y ∉ l.f ∪ l.i) :
      TypingStepₘ (Typing.cut L huniq) l (Typing.cut L huniq')

instance {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} :
  HasStep (Typing n P 𝒢) Lbl (Typing n' P' 𝒢') where
  step 𝒟 l 𝒟' := TypingStepₘ 𝒟 l 𝒟'

theorem TypingStepₘ.preserves_WF {n n' 𝒢 𝒢' P P'}
  (𝒟 : n ⊢ P ∷ 𝒢) (𝒟' : n' ⊢ P' ∷ 𝒢') (l : Lbl) :
  TypingStepₘ 𝒟 l 𝒟' → l.WF := by
  intro h
  induction h <;> simp_all only [Lbl.WF]
  case res L _ _ _ _  ih =>
    obtain ⟨x, hx, y, hy, hneq⟩ := exists_two_fresh L
    have := ih x hx y hy hneq
    exact this

-- theorem TypingStep.preserves_serverUsableEnv

inductive MTSTₘ : {n n' : Nat} → {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
  Typing n P 𝒢 → Lbls → Typing n' P' 𝒢' → Prop where
  | refl {n : Nat} {P : Proc} {𝒢 : HyperEnv} {𝒟 : Typing n P 𝒢} :
    MTSTₘ 𝒟 (ε) 𝒟

  | stepR {n n' n'' : Nat} {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
    (𝒟  : Typing n P 𝒢) (𝒟' : Typing n' P' 𝒢') (𝒟'' : Typing n'' P'' 𝒢'') :
    (MTSTₘ 𝒟 ls 𝒟'') → (𝒟'' -[l]-> 𝒟') →
    -------------------------------------
          MTSTₘ 𝒟 (ls ∷ₗ l) 𝒟'

instance {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} :
  HasMultiStep (Typing n P 𝒢) Lbls (Typing n' P' 𝒢') where
  step 𝒟 l 𝒟' := MTSTₘ 𝒟 l 𝒟'

inductive EnvStepₘ : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : FPName} :
      EnvStepₘ [[x ∶ 1]] (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ]) :
      EnvStepₘ [x ∶ A ⨂ B :: Γ‚ Δ] (x⟦x'⟧) ([x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ])

  | bot
      {Γ : Env} {x : FPName} :
      EnvStepₘ [x ∶ ⊥ :: Γ] (x⸨⸩) [Γ]

  | parr
      {Γ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⅋ B :: Γ]) :
      EnvStepₘ [x ∶ A ⅋ B :: Γ] (x⸨x'⸩) [x' ∶ A :: x ∶ B :: Γ]

  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStepₘ 𝒢 l 𝒢' →
      -----------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStepₘ ℋ l ℋ' →
      -----------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStepₘ 𝒢 l 𝒢' → EnvStepₘ ℋ l' ℋ' →
      --------------------------------------------------
      EnvStepₘ (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')

  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
      EnvStepₘ (𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ [Γ]) →
      ---------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ]) (τ) (𝒢 |ₕ [Γ])

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': FPName} {A B : Types} :
      EnvStepₘ
        (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ]) →
      ------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ‚ Ξ]) (τ) (𝒢 |ₕ [Γ‚ Δ‚ Ξ])

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A : Types} {l : Lbl} :
      EnvStepₘ (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) (l) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])

instance : HasStep HyperEnv Lbl HyperEnv where step := EnvStepₘ

theorem session_fidelity_envₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'}
  (hStep : TypingStepₘ 𝒟 l 𝒟') : EnvStepₘ (env 𝒟) l (env 𝒟') := by
  induction hStep

  case one | bot => constructor

  case tensor y _ _ _ _ _ hy 𝒟' =>
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity (𝒟' y hy)
    have hD := HyperEnv.PairwiseDisjoint_implies_disjoint hpw
    simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, not_or,
      Finset.disjoint_insert_left, ← ne_eq] at hD
    simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
    obtain ⟨⟨hxy, hxΓ⟩, hyΔ, hDΓΔ⟩ := hD
    obtain ⟨⟨hyΓ, hndΓ⟩, ⟨hxΔ, hndΔ⟩⟩ := hnd
    apply EnvStepₘ.tensor
    simp only [HyperEnv.names_distributes, Env.names_distributes, Finset.notMem_union,
      Finset.notMem_singleton, Env.names_merge, HyperEnv.names_nil]
    split_ands
    · exact hxy.symm
    · exact hyΓ
    · exact hyΔ
    · simp only [Finset.notMem_empty, not_false_eq_true]

  case parr y _ _ _ _ _ hy 𝒟' =>
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity (𝒟' y hy)
    simp only [HyperEnv.Nodup_singleton, Env.names_distributes, Env.Nodup_cons,
      Finset.notMem_union, Finset.notMem_singleton] at hnd
    apply EnvStepₘ.parr
    simp only [HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty, Finset.mem_insert, not_or, hnd.1,
      not_false_eq_true, true_and]

  case par₁ ih | par₂ ih =>
    constructor
    exact ih

  case syn ih1 ih2 => exact EnvStepₘ.syn ih1 ih2

  case one_bot L _ _ _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    have ih' := ih x y hx hy hneq
    simp only [Env.cons_nil, Env.merge_unitL] at ih' ⊢
    exact EnvStepₘ.one_bot (x := x) (y := y) ih'

  case tensor_parr 𝒥 Γ Δ Ξ _ _ A B _ L _ _ _ _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    obtain ⟨x', y', hx', hy', hneq'⟩ := exists_two_fresh (L ∪ {x} ∪ {y})
    simp [← ne_eq] at hx' hy'
    obtain ⟨hxx', hyx', hx'⟩ := hx'
    obtain ⟨hxy', hyy', hy'⟩ := hy'
    have ih' := ih x y hx hy hneq x' y' hx' hy' hneq' hxx'.symm hxy'.symm hyx'.symm hyy'.symm
    exact EnvStepₘ.tensor_parr ih'

  case res 𝒥 𝒥' Γ Γ' Δ Δ' _ _ A _ _ L _ _ _ _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    have ih' := ih x y hx hy hneq
    apply EnvStepₘ.res ih'


inductive ProcStepₘ : (P : Proc) → Lbl → (P' : Proc) → Prop where
  | one
      {P : Proc} {x : FPName} :
      ProcStepₘ (#x⟦⟧․P) (x⟦⟧) P

  | tensor
      {P : Proc} {x y : FPName} (hF : y ∉ {x} ∪ P.f) :
      ProcStepₘ (#x⟦$N⟧․P) (x⟦y⟧) P⸨#y⸩

  | bot
      {P : Proc} {x : FPName} :
      ProcStepₘ (#x⸨⸩․P) (x⸨⸩) P

  | parr
      {P : Proc} {x y : FPName} (hF: y ∉ {x} ∪ P.f) :
      ProcStepₘ (#x⸨$N⸩․P) (x⸨y⸩) P⸨#y⸩

  | par₁
      {P P' Q : Proc} {l : Lbl} :
      ProcStepₘ P l P' → l.i ∩ Q.f = ∅ →
      ----------------------------------
      ProcStepₘ (P |ₚ Q) l (P' |ₚ Q)

  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStepₘ Q l Q' → l.i ∩ P.f = ∅ →
      ----------------------------------
      ProcStepₘ (P |ₚ Q) l (P |ₚ Q')

  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStepₘ P l P' → ProcStepₘ Q l' Q' →
      (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  → (l |ₗ l').WF →
      ---------------------------------------------
      ProcStepₘ (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

  | one_bot
      {P P' : Proc} (L : Finset FPName) :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      ProcStepₘ P⸨#x, #y⸩ (x⟦⟧ |ₗ y⸨⸩) P') →
      ----------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (τ) P'

  | tensor_parr
      {P P' : Proc} {x x' y y' : FPName} {L : Finset FPName} :
      (∀ x ∉ L, ∀ x' ∉ L, ∀ y ∉ L, ∀ y' ∉ L,
      x ≠ x' → x ≠ y → x ≠ y' → y ≠ x' → y ≠ y' → x' ≠ y' →
      ProcStepₘ P⸨#x, #y⸩ (x⟦x'⟧ |ₗ y⸨y'⸩) P'⸨#x, #y⸩⸨#x', #y'⸩) →
      ---------------------------------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (τ) (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P'))

  | res
      {P P' : Proc} {l : Lbl} {L : Finset FPName} :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      ProcStepₘ P⸨#x, #y⸩ l P'⸨#x, #y⸩) →
      -------------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (l) (𝑣⸨$N,$N⸩ P')



theorem session_fidelity_procₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'}
  (hStep : TypingStepₘ 𝒟 l 𝒟') : ProcStepₘ P l P' := by
  induction hStep
  all_goals sorry


theorem typability_subject_reductionₘ
  {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
  (𝒟 : Typing n P 𝒢)
  (hPS : ProcStepₘ P l P') :
  ∃ (n' : Nat) (𝒢' : HyperEnv) (𝒟' : Typing n' P' 𝒢'),
    TypingStepₘ 𝒟 l 𝒟' := by
  induction hPS generalizing n 𝒢
  all_goals sorry


/- NOTE FOR PAPER
The res rule in fig 5 and the res rule in fig 2, has swapped which name is typed with Aᗮ, visually
this could induce some confusion, but theoretically it shoulnd't have any impact.(since to make them
match again one could just pass Aᗮ as the type to either in which case the ordering would swap.)
-/

-- TODO: Prove Session fidelity, erasure, type preservation, Session fidelity for πLL
