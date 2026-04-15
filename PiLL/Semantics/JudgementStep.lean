import PiLL.Substitution
import PiLL.Semantics.Labels

-- Same reason as in Environment.lean
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

lemma Typing_tensor_all_fresh {n : Nat} {P : Proc} {Γ Δ : Env}
  {x : FPName} {A B : Types} {L : Finset FPName}
  (hT : ∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) :
  ∀ y, y ∉ ({x} ∪ P.f ∪ Γ.names ∪ Δ.names) →
  Typing n (P⸨#y⸩) ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ]) := by
  intro y hy
  obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ {x} ∪ P.f ∪ Γ.names ∪ Δ.names)
  simp only [Finset.union_singleton, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq, Finset.notMem_singleton] at hz hy
  have 𝒟z := hT z hz.2.2.1
  have 𝒟y := Typing_substNames 𝒟z (y := y) (x := z) ?_
  · simp only [List.cons_append, List.nil_append, HyperEnv.substNames_distributes,
    Env.substNames_distributes, FPName.subst_self, HyperEnv.names_nil, Finset.notMem_empty,
    not_false_eq_true, HyperEnv.substNames_of_not_mem] at 𝒟y
    rw [Env.substNames_of_not_mem hz.2.2.2.2.1, Env.substNames_of_not_mem hz.2.2.2.2.2,
      FPName.subst_self_of_ne hz.1.symm, Proc.open_substNames,
      Proc.substNames_of_not_mem hz.2.2.2.1, FPName.subst_self] at 𝒟y
    exact 𝒟y
  · intro Ξ hΞ C hyΞ
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hΞ
    rcases hΞ with rfl | rfl
    · simp only [List.mem_cons, Prod.mk.injEq] at hyΞ
      rcases hyΞ with ⟨rfl, hCA⟩ | hin
      · rfl
      · exfalso ; exact hy.2.2.1 (Env.mem_pair_fst_in_names _ hin)
    · simp only [List.mem_cons, Prod.mk.injEq] at hyΞ
      rcases hyΞ with ⟨rfl, rfl⟩ | hin
      · exfalso ; apply hy.1 ; rfl
      · exfalso ; apply hy.2.2.2 (Env.mem_pair_fst_in_names _ hin)

lemma Typing_parr_all_fresh {n : Nat} {P : Proc} {Γ : Env}
  {x : FPName} {A B : Types} {L : Finset FPName}
  (hT : ∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: x ∶ B :: Γ])) :
  ∀ y, y ∉ ({x} ∪ P.f ∪ Γ.names) →
  Typing n (P⸨#y⸩) ([y ∶ A :: x ∶ B :: Γ]) := by
  intro y hy
  obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ {x} ∪ P.f ∪ Γ.names)
  simp only [Finset.union_singleton, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq, Finset.notMem_singleton] at hz hy
  have 𝒟z := hT z hz.2.2.1
  have 𝒟y := Typing_substNames 𝒟z (y := y) (x := z) ?_
  · simp only [HyperEnv.substNames_distributes, Env.substNames_distributes] at 𝒟y
    rw [Proc.open_substNames, Proc.substNames_of_not_mem hz.2.2.2.1, FPName.subst_self,
      FPName.subst_self_of_ne hz.1.symm, Env.substNames_of_not_mem hz.2.2.2.2,
      HyperEnv.substNames_of_not_mem] at 𝒟y
    · exact 𝒟y
    · rw [HyperEnv.names_nil] ; apply Finset.notMem_empty
  · intro Ξ hΞ C hin
    simp_all only [ne_eq, Env.mem_pair_fst_in_names_iff, not_exists, not_false_eq_true,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, false_and, or_self]


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
      {hF: x ∉ Γ.names ∧ x ∉ Δ.names} {L : Finset FPName}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])}
      {hy : y ∉ ({x} ∪ P.f ∪ Γ.names ∪ Δ.names)} :
      TypingStepₘ (Typing.tensor hF L huniq) (x⟦y⟧) (Typing_tensor_all_fresh huniq y hy)

  | parr
      {Γ : Env} {P : Proc} {x y : FPName} {A B : Types} {n : Nat}
      {hF : x ∉ Γ.names} {L : Finset FPName}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) [z ∶ A :: x ∶ B :: Γ]}
      {hy : y ∉ ({x} ∪ P.f ∪ Γ.names)} :
      TypingStepₘ (Typing.parr hF L huniq) (x⸨y⸩) (Typing_parr_all_fresh huniq y hy)

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
      {x y : FPName} (hxL : x ∉ L) (hyL : y ∉ L) (hneq : x ≠ y)
      (hxP : x ∉ P.f) (hyP : y ∉ P.f)
      {𝒟' : Typing n P' (𝒢 |ₕ [Env.merge ∅ Γ])}
      (hStep : TypingStepₘ (huniq x y hxL hyL hneq) (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
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
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      {x' y' : FPName} (hx' : x' ∉ L) (hy' : y' ∉ L) (hneq' : x' ≠ y')
      (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x') (hyy' : y ≠ y')
      (hxP : x ∉ P.f) (hyP : y ∉ P.f) (hx'P : x' ∉ P.f) (hy'P : y' ∉ P.f)
      (hStep : TypingStepₘ (huniq x y hx hy hneq) (x⟦x'⟧ |ₗ y⸨y'⸩)
                (huniq' x y hx hy hneq x' y' hx' hy' hneq' hxx' hxy' hyx' hyy')) :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

| res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {A : Types} {n : Nat} {l : Lbl}
      {L : Finset FPName}
      {huniq : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])}
      {huniq' : ∀ x y, x ∉ L → y ∉ L → x ≠ y →
                Typing n (P'⸨#x, #y⸩) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'])}
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      (hFx : x ∉ P.f ∪ l.f ∪ l.i) (hFy : y ∉ P.f ∪ l.f ∪ l.i)
      (hStep : TypingStepₘ (huniq x y hx hy hneq) l (huniq' x y hx hy hneq)) :
      TypingStepₘ (Typing.cut L huniq) l (Typing.cut L huniq')

  ------- Additional Structural / Exchange Rules -------

  | perm {𝒢 ℋ 𝒢' : HyperEnv} {P P' : Proc} {n n' : Nat} {l : Lbl}
    {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
    (hPerm : 𝒢 ~ ℋ) (hTS : TypingStepₘ 𝒟 l 𝒟') :
    TypingStepₘ (Typing.exchange_hyper 𝒟 hPerm) l 𝒟'

instance {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} :
  HasStep (Typing n P 𝒢) Lbl (Typing n' P' 𝒢') where
  step 𝒟 l 𝒟' := TypingStepₘ 𝒟 l 𝒟'

theorem TypingStepₘ.preserves_WF {n n' 𝒢 𝒢' P P'}
  (𝒟 : n ⊢ P ∷ 𝒢) (𝒟' : n' ⊢ P' ∷ 𝒢') (l : Lbl) :
  TypingStepₘ 𝒟 l 𝒟' → l.WF := by
  intro h
  induction h <;> simp_all only [Lbl.WF]
  -- case res L _ _ _ _  ih =>
  --   obtain ⟨x, hx, y, hy, hneq⟩ := exists_two_fresh L
  --   have := ih x hx y hy hneq
  --   exact this

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

  ------- Additional Structural / Exchange Rules -------s

  | perm {𝒢 ℋ 𝒢' : HyperEnv} {l : Lbl} (hPerm : 𝒢 ~ ℋ)  (hES : EnvStepₘ 𝒢 l 𝒢') :
      EnvStepₘ ℋ l 𝒢'

instance : HasStep HyperEnv Lbl HyperEnv where step := EnvStepₘ

-- env: Der → Env (HyperEnv)
theorem session_fidelity_envₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟') :
  EnvStepₘ (env 𝒟) l (env 𝒟') := by
  induction hStep

  case one | bot => constructor

  case tensor y _ _ _ _ L 𝒟' hy =>
    have ⟨z, hz⟩ := exists_one_fresh L
    have 𝒟y := Typing_tensor_all_fresh 𝒟' y hy
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟y
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

  case parr y _ _ _ _ L 𝒟' hy =>
    have ⟨z, hz⟩ := exists_one_fresh L
    have 𝒟y := Typing_parr_all_fresh 𝒟' y hy
    obtain ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟y
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

  case one_bot ih =>
    exact EnvStepₘ.one_bot ih

  case tensor_parr ih =>
    exact EnvStepₘ.tensor_parr ih

  case res ih =>
    exact EnvStepₘ.res ih


  case perm hP hTS ih => exact EnvStepₘ.perm hP ih

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
      {P P' : Proc} {x y : FPName} (hx : x ∉ P.f) (hy : y ∉ P.f) (hneq : x ≠ y) :
      ProcStepₘ P⸨#x, #y⸩ (x⟦⟧ |ₗ y⸨⸩) P' →
      -----------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (τ) P'

| tensor_parr
      {P P' : Proc} {x x' y y' : FPName}
      (hx : x ∉ P.f) (hx' : x' ∉ P.f) (hy : y ∉ P.f) (hy' : y' ∉ P.f)
      (hxx' : x ≠ x') (hxy : x ≠ y) (hxy' : x ≠ y')
      (hyx' : y ≠ x') (hyy' : y ≠ y') (hx'y' : x' ≠ y')
      (hStep : ProcStepₘ P⸨#x, #y⸩ (x⟦x'⟧ |ₗ y⸨y'⸩) P'⸨#x, #y⸩⸨#x', #y'⸩) :
      ---------------------------------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (τ) (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P'))

| res
      {P P' : Proc} {l : Lbl} {x y : FPName}
      (hx : x ∉ P.f ∪ l.f ∪ l.i) (hy : y ∉ P.f ∪ l.f ∪ l.i) (hneq : x ≠ y)
      (hStep : ProcStepₘ P⸨#x, #y⸩ l P'⸨#x, #y⸩) :
      -------------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (l) (𝑣⸨$N,$N⸩ P')

-- proc: Der → Proc
theorem session_fidelity_procₘ
  {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} {l : Lbl}
  {𝒟 : Typing n P 𝒢} {𝒟' : Typing n' P' 𝒢'} (hStep : TypingStepₘ 𝒟 l 𝒟') :
  ProcStepₘ (proc 𝒟) l (proc 𝒟') := by
  induction hStep

  case one | bot => constructor

  case tensor Q _ y _ _ _ _ L ih hy =>
    have ⟨z, hz⟩ := exists_one_fresh (L ∪ {y})
    simp [← ne_eq] at hz
    obtain ⟨hzy, hz⟩ := hz
    have 𝒟y := Typing_tensor_all_fresh ih y hy
    have hfn := Typing.f_eq_names (ih z hz)
    have ⟨hnd, hpw⟩:= Typing_preserves_linearity 𝒟y
    have hD := HyperEnv.PairwiseDisjoint_implies_disjoint hpw
    simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, not_or,
      Finset.disjoint_insert_left, ← ne_eq] at hD
    simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
    obtain ⟨⟨hxy, hxΓ⟩, ⟨hyΔ, hDΓΔ⟩⟩ := hD
    obtain ⟨⟨hyΓ, hndΓ⟩, ⟨hxΔ, hndΔ⟩⟩ := hnd
    have h1 : y ∉ Q⸨#z⸩.f := by
      rw [hfn]
      simp only [List.cons_append, List.nil_append, HyperEnv.names_cons,
        Env.names_distributes, Finset.singleton_union, HyperEnv.names_nil,
        Finset.union_empty, Finset.union_insert, Finset.insert_union,
        Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq]
      exact ⟨hxy.symm, hzy.symm, hyΓ, hyΔ⟩
    have h2 := Proc.f_subset_open (P := Q) (x := z)
    apply ProcStepₘ.tensor
    simp
    constructor
    · exact hxy.symm
    · intro hy
      exact h1 ((Finset.subset_iff.mp h2) hy)

  case parr Q _ y _ _ _ _ L ih hy =>
    have ⟨z, hz⟩ := exists_one_fresh (L ∪ {y})
    simp [← ne_eq] at hz
    obtain ⟨hzy, hz⟩ := hz
    have 𝒟y := Typing_parr_all_fresh ih y hy
    have hfn := Typing.f_eq_names (ih z hz)
    have ⟨hnd, hpw⟩:= Typing_preserves_linearity 𝒟y
    simp only [HyperEnv.Nodup_singleton, Env.names_distributes, Env.Nodup_cons,
      Finset.notMem_union, Finset.notMem_singleton] at hnd
    obtain ⟨⟨hyx, hyΓ⟩, ⟨hxΓ, hndΓ⟩⟩ := hnd
    have h1 : y ∉ Q⸨#z⸩.f := by
      rw [hfn]
      simp only [HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
        HyperEnv.names_nil, Finset.union_empty, Finset.union_insert, Finset.mem_insert,
        not_or, ← ne_eq]
      exact ⟨hyx, hzy.symm, hyΓ⟩
    have h2 := Proc.f_subset_open (P := Q) (x := z)
    apply ProcStepₘ.parr
    simp
    constructor
    · exact hyx
    · intro hy
      exact h1 ((Finset.subset_iff.mp h2) hy)

  case par₁ hD ih | par₂ hD ih =>
    constructor
    · exact ih
    · exact hD

  case syn hD lwf ih1 ih2 => exact ProcStepₘ.syn ih1 ih2 hD lwf

  case one_bot hneq hxP hyP _ _ ih =>
    exact ProcStepₘ.one_bot hxP hyP hneq ih

  case tensor_parr hxy _ _ _ _ hx'y' hxx' hxy' hyx' hyy' hxP hyP hx'P hy'P _ ih =>
    exact ProcStepₘ.tensor_parr hxP hx'P hyP hy'P hxx' hxy hxy' hyx' hyy' hx'y' ih

  case res hneq hFx hFy _ ih =>
    exact ProcStepₘ.res hFx hFy hneq ih

  case perm hP hTS ih => exact ih


-- FIXME: Move to Process
lemma Proc.not_mem_f_open {P : Proc} {y z : FPName}
  (hzy : z ≠ y) (hfz : z ∉ P.f) (hy : y ∉ P.f) :
  y ∉ P⸨#z⸩.f := by
  intro hc
  have h_erased := Finset.mem_erase.mpr ⟨hzy.symm, hc⟩
  rw [Proc.f_open_erase hfz] at h_erased
  exact hy h_erased



-- FIXME: Move to Labels
lemma Lbl.f_par' {a a' : Act} :
  (a |ₗ a').f =  (Lbl.act a).f ∪ (Lbl.act a').f := by simp only [f]

lemma Lbl.i_par' {a a' : Act} :
  (a |ₗ a').i =  (Lbl.act a).i ∪ (Lbl.act a').i := by simp only [i]

-- FIXME: Move to Environment
lemma Env.disjoint_cons_iff {Γ Δ : Env} {x y : FPName} {A : Types} :
  Disjoint (Env.names (x ∶ A :: Γ)) (Env.names (y ∶ Aᗮ :: Δ)) ↔
  (y ≠ x ∧ y ∉ Γ.names ∧ x ∉ Δ.names ∧ Disjoint Γ.names Δ.names) := by
  simp only [Env.names_distributes, Finset.singleton_union, Finset.disjoint_insert_right,
    Finset.mem_insert, not_or, ← ne_eq, Finset.disjoint_insert_left]
  constructor
  · intro h
    rcases h with ⟨⟨hneq, hyΓ⟩, ⟨hxΔ, hDΓΔ⟩⟩
    refine ⟨hneq, hyΓ, hxΔ, hDΓΔ⟩
  · intro h
    rcases h with ⟨hneq, hyΓ, hxΔ, hDΓΔ⟩
    refine ⟨⟨hneq, hyΓ⟩, ⟨hxΔ, hDΓΔ⟩⟩

lemma Env.Perm.eq_nil_of_disjoint {Γ Δ : Env} (hD : Γ.disjoint Δ) (hP : Γ.Perm Δ) :
  Γ = [] ∧ Δ = [] := by
  induction hP
  case nil => simp
  case cons E Γ Δ hP ih =>
    rcases E with ⟨x, A⟩
    simp only [disjoint, names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, true_or,
      not_true_eq_false, Finset.disjoint_insert_left,false_and] at hD
  case swap E1 E2 Γ => rcases E1 ; rcases E2 ; simp at hD
  case trans l1 l2 l3 hP1 hP2 ih1 ih2 =>
    simp [Disjoint] at hD
    have hNamesEq := Env.names_eq_of_perm (hP1.trans hP2)
    have hEmptyNames : names l1 = ∅ := by
      apply hD (x := names l1)
      · simp only [subset_refl]
      · rw [← hNamesEq]
    have h1 : l1 = [] := by simp_all
    have h2 : l3 = [] := by simp_all
    refine ⟨h1, h2⟩







-- FIXME: Move to judgement
lemma Typing_res_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env}
  {x y : FPName} {A B : Types}
  (𝒟 : Typing n P (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])) :
  (x ∉ 𝒢.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names) ∧
  (y ∉ 𝒢.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names) := by
  have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
  simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
  obtain ⟨⟨_, hxΓ, _⟩, hyΔ, _⟩ := hnd
  rw [HyperEnv.merge_assoc] at hpw
  have hD := HyperEnv.PairwiseDisjoint_tail_not_in_head hpw
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, Prod.mk.injEq, forall_eq] at hD
  obtain hx𝒢 := hD.1 x A (Or.inl ⟨rfl, rfl⟩)
  obtain hy𝒢 := hD.2 y B (Or.inl ⟨rfl, rfl⟩)
  simp only [HyperEnv.PairwiseDisjoint_merge] at hpw
  have := HyperEnv.PairwiseDisjoint_implies_disjoint
    (HyperEnv.PairwiseDisjoint_merge.mpr hpw.2.1)
  obtain ⟨hxy, hyΓ, hxΔ, hDΓΔ⟩ := Env.disjoint_cons_iff.mp this
  refine ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩

lemma TypingStepₘ_names_bound {n n' P P' 𝒢 𝒢' l} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 l 𝒟') :
  𝒢'.names ⊆ 𝒢.names ∪ l.i := by
  induction hStep

  case one | bot | tensor | parr | one_bot | tensor_parr => simp

  case par₁ ih =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢' | hyℋ
    · have := ih hy𝒢'
      simp [- Lbl.i] at this
      rcases this with h1 | h2
      · simp [h1]
      · simp [- Lbl.i, h2]
    · simp [hyℋ]

  case par₂ ih =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢 | hyℋ'
    · simp [hy𝒢]
    · have := ih hyℋ'
      simp [- Lbl.i] at this
      rcases this with h1 | h2
      · simp [h1]
      · simp [- Lbl.i, h2]

  case syn ih1 ih2 =>
    simp only [HyperEnv.names_merge]
    intro y hy
    simp only [Finset.mem_union] at hy ⊢
    rcases hy with hy𝒢' | hyℋ'
    · have := ih1 hy𝒢'
      simp [- Lbl.i] at this
      rcases this with h1 | h2
      · simp [h1]
      · simp [Lbl.i_par', - Lbl.i, h2]
    · have := ih2 hyℋ'
      simp [- Lbl.i] at this
      rcases this with h1 | h2
      · simp [h1]
      · simp [- Lbl.i, Lbl.i_par', h2]

  case res 𝒢' _ Γ' _ Δ' _ _ A _ _ _ _ huniq' x y hx hy hneq hFx hFy hStep ih =>
    intro a ha
    simp only [HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge, HyperEnv.names_nil,
      Finset.union_empty, Finset.mem_union, List.append_assoc, List.cons_append,
      List.nil_append, Env.names_distributes, Finset.singleton_union, Finset.union_insert,
      Finset.insert_union, Finset.union_assoc] at ha ih ⊢
    have haLHS : a ∈ insert y (insert x (𝒢'.names ∪ (Γ'.names ∪ Δ'.names))) := by
      simp only [Finset.mem_insert, Finset.mem_union, ha, or_true]
    have haRHS := ih haLHS
    simp only [Finset.mem_insert, Finset.mem_union] at haRHS
    have ⟨⟨hx𝒢', hxΓ', hxΔ'⟩, ⟨hy𝒢', hyΓ', hyΔ'⟩⟩ := Typing_res_fresh (huniq' x y hx hy hneq)
    rcases haRHS with rfl | rfl | h
    · rcases ha with h1 | h2 | h3
      · exfalso ; apply hy𝒢' h1
      · exfalso ; apply hyΓ' h2
      · exfalso ; apply hyΔ' h3
    · rcases ha with h1 | h2 | h3
      · exfalso ; apply hx𝒢' h1
      · exfalso ; apply hxΓ' h2
      · exfalso ; apply hxΔ' h3
    · exact h

  case perm hP _ ih =>
    rw [← (HyperEnv.names_eq_of_perm hP)]
    exact ih

lemma TypingStepₘ_par_preserves_disjoint {n : Nat} {Q Q' R : Proc} {𝒥 𝒥' 𝒦 : HyperEnv} {l' : Lbl}
  {hTQ : n ⊢ Q ∷ 𝒥} {hTQ' : n ⊢ Q' ∷ 𝒥'} (hTR : n ⊢ R ∷ 𝒦)
  (hStep : TypingStepₘ hTQ l' hTQ') (hD : 𝒥.disjoint 𝒦) (disj : l'.i ∩ R.f = ∅) :
  𝒥'.disjoint 𝒦 := by
    have hsub := TypingStepₘ_names_bound hStep
    simp [- Lbl.i] at hsub hD
    have hnf := Typing.f_eq_names hTR
    have : Disjoint (𝒥.names ∪ l'.i) 𝒦.names := by
      simp [- Lbl.i, hD, hnf] at disj ⊢
      exact Finset.disjoint_iff_inter_eq_empty.mpr disj
    exact Disjoint.mono_left hsub this

lemma TypingStepₘ_syn_preserves_disjoint {n : Nat} {P P' Q Q' : Proc}
  {𝒥 𝒥' 𝒦 𝒦' : HyperEnv} {l' l'' : Act} {hTP : n ⊢ P ∷ 𝒥} {hTP' : n ⊢ P' ∷ 𝒥'}
  {hTQ : n ⊢ Q ∷ 𝒦} {hTQ' : n ⊢ Q' ∷ 𝒦'} (hStepPP' : TypingStepₘ hTP l' hTP')
  (hStepQQ' : TypingStepₘ hTQ l'' hTQ') (hD : 𝒥.disjoint 𝒦)
  (disj : (l' |ₗ l'').i ∩ (P |ₚ Q).f = ∅) (lwf : (l' |ₗ l'').WF) :
  𝒥'.disjoint 𝒦' := by
  have hsubRR' := TypingStepₘ_names_bound hStepPP'
  have hsubQQ' := TypingStepₘ_names_bound hStepQQ'
  have hlwf := Finset.disjoint_iff_inter_eq_empty.mpr lwf
  have hdisj := Finset.disjoint_iff_inter_eq_empty.mpr disj
  have hnfR := Typing.f_eq_names hTP
  have hnfQ := Typing.f_eq_names hTQ
  simp only [Proc.f_par, Lbl.i_par'] at hdisj
  simp only [hnfR, hnfQ, Finset.disjoint_union_left, Finset.disjoint_union_right] at hdisj
  rcases hdisj with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  apply Disjoint.mono hsubRR' hsubQQ'
  simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
  refine ⟨⟨hD, h3⟩, h2.symm, hlwf⟩







lemma HyperEnv.Perm.extract_one_res_source
  {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [[z ∶ 1]])
  (hxz : x ≠ z) (hyz : y ≠ z) :
  ∃ 𝒢ᵣ_new,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[z ∶ 1]] := by
  have hzin : ([z ∶ 1]) ∈ 𝒢ᵣ |ₕ [[z ∶ 1]] := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hzin
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ : ∃ 𝒢ᵣ, 𝒢 ~ E :: 𝒢ᵣ :=
        HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' : 𝒢 ~ [z ∶ 1] :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], ?_⟩
      have := h𝒢_split.symm.trans h𝒢'
      apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm.merge
      · rw [HyperEnv.cons_append] at h𝒢'
        exact h𝒢'
      · rfl
    case inr h =>
      rw [h] at hPE
      simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
      rw [hPE.1.1] at hxz
      contradiction
  · exfalso
    simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
    rw [hPE.1.1] at hyz
    contradiction

lemma HyperEnv.Perm.extract_bot_res_source
  {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ Ξ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
  (hxz : x ≠ z) (hyz : y ≠ z)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ_new Γᵣ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γᵣ] := by
  have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · rcases h with hE𝒢 | hEΓx
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ξz : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Ξ, ?_⟩
      apply HyperEnv.Perm.trans
      · exact HyperEnv.Perm.merge_right h𝒢Ξz [Γ‚ Δ]
      · have := (HyperEnv.Perm_merge_singleton (z ∶ ⊥ :: Ξ) (𝒢ᵣ' |ₕ [Γ‚ Δ])).symm
        rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
        exact this
    · subst hEΓx
      have hzinΓx : (z, ⊥) ∈ x ∶ Aᗮ :: Γ := by
        simp [HasPerm.perm] at hPE
        have h := hPE.symm.subset
        simp at h
        obtain ⟨hL, hR⟩ := h
        cases hL
        case inl hL1 =>
          rw [hL1.1, hL1.2]
          simp
        case inr hL2 =>
          exact List.mem_cons.mpr (Or.inr hL2)
      simp at hzinΓx
      rcases hzinΓx with ⟨hzx_eq, _⟩ | hin
      · subst hzx_eq
        contradiction
      · obtain ⟨Γᵣ, hΓ_split⟩ : ∃ Γᵣ, Γ ~ (z, ⊥) :: Γᵣ := Env.exists_perm_cons hin
        refine ⟨𝒢, (Γᵣ ++ Δ), ?_⟩
        apply HyperEnv.Perm.merge_left
        exact (HyperEnv.Perm.cons (List.Perm.append_right Δ hΓ_split) (by rfl))
  · have hzinΔy : (z, ⊥) ∈ y ∶ A :: Δ := by
      simp [HasPerm.perm] at hPE
      have h := hPE.symm.subset
      simp at h
      obtain ⟨hL, hR⟩ := h
      cases hL
      case inl hL1 =>
        rw [hL1.1, hL1.2]
        simp
      case inr hL2 =>
        exact List.mem_cons.mpr (Or.inr hL2)
    simp at hzinΔy
    rcases hzinΔy with ⟨hzy_eq, _⟩ | hin
    · subst hzy_eq
      contradiction
    · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (z, ⊥) :: Δᵣ := Env.exists_perm_cons hin
      refine ⟨𝒢, (Γ ++ Δᵣ), ?_⟩
      apply HyperEnv.Perm.merge_left
      apply HyperEnv.Perm.cons
      · have hP1 := List.Perm.append_right Γ hΔ_split
        have hP2 : Γ ++ Δ ~ Δ ++ Γ := by
          simp [HasPerm.perm]
          apply List.perm_append_comm
        have hP3 : ((z, ⊥) :: Δᵣ ++ Γ) ~ ((z, ⊥) :: Γ ++ Δᵣ) := by
          apply List.Perm.cons
          exact List.perm_append_comm
        exact (hP2.trans hP1).trans hP3
      · rfl

lemma HyperEnv.Perm.extract_one_bot_res_source
  {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ Ξ : Env} {u v x y : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ])
  (hux : u ≠ x) (hvx : v ≠ x) (huy : u ≠ y) (hvy : v ≠ y)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hneq : u ≠ v) (hvΓ : v ∉ Γ.names) (huΔ : u ∉ Δ.names) :
  ∃ 𝒢ᵣ_new Γᵣ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by
  have hxin : ([x ∶ 1]) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hxin
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' := h𝒢_split.trans (HyperEnv.Perm.cons hPE (.refl _))
      have h_pre_bot : 𝒢ᵣ' |ₕ [u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ] := by
        have := HyperEnv.Perm.merge_right h𝒢' ([u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ])
        rw [← HyperEnv.merge_assoc] at this
        have := this.symm.trans h_pre
        apply HyperEnv.Perm_rotate_rhs_right at this
        rw [HyperEnv.merge_assoc, ← HyperEnv.cons_append, ← HyperEnv.cons_append] at this
        apply HyperEnv.Perm.cons_cancel_left at this
        rw [← HyperEnv.merge_nilR (𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ])]
        apply HyperEnv.Perm_rotate_rhs_left
        simp only [List.append_eq, List.cons_append, List.nil_append,
          List.append_assoc, List.append_nil] at ⊢ this
        exact this
      simp only [HasPerm.perm, List.perm_singleton] at hPE
      subst hPE
      have hFuᵣ : u ∉ HyperEnv.names 𝒢ᵣ':= by
        intro hc
        exact hFu (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
      have hFvᵣ : v ∉ HyperEnv.names 𝒢ᵣ' := by
        intro hc
        exact hFv (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
      obtain ⟨𝒢ᵣ'', Γₙ, h_pre'⟩ :=
        HyperEnv.Perm.extract_bot_res_source h_pre_bot huy hvy hFuᵣ hFvᵣ hneq huΔ hvΓ
      refine ⟨𝒢ᵣ'', Γₙ, ?_⟩
      · have h1 := HyperEnv.Perm.merge_right h𝒢_split ([Γ‚ Δ])
        have h2 := HyperEnv.Perm.merge_right h_pre' ([[x ∶ 1]])
        conv_rhs at h1 => rw [HyperEnv.cons_append]
        apply HyperEnv.Perm_rotate_rhs_right at h1
        conv_rhs at h2 => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h2
        rw [← HyperEnv.merge_assoc] at h2
        apply HyperEnv.Perm_rotate_rhs_right at h2
        exact h1.trans h2
    case inr h =>
      subst h
      simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
      obtain ⟨⟨h1, _⟩, _⟩ := hPE
      subst h1
      contradiction
  · simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
    obtain ⟨⟨h1, _⟩, _⟩ := hPE
    subst h1
    contradiction




lemma TypingStepₘ_inv_one_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧) 𝒟') :
  ∃ 𝒢ᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]] := by
  generalize hl : (x⟦⟧ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl

  case one =>
    subst hl
    use ∅
    rw [HyperEnv.merge_unitL]

  case par₁ ih =>
    expose_names
    simp [HasBracket.brack] at ih
    have ⟨𝒢'', hP⟩ := ih hl
    use ℋ |ₕ 𝒢''
    apply HyperEnv.Perm_exchange_lhs HyperEnv.Perm.merge_comm
    rw [HyperEnv.merge_assoc]
    exact HyperEnv.Perm_merge_cancel_left_inv hP

  case par₂ ih =>
    expose_names
    simp [HasBracket.brack] at ih
    have ⟨ℋ''', hP⟩ := ih hl
    use 𝒢_1 |ₕ ℋ'''
    rw [HyperEnv.merge_assoc]
    exact HyperEnv.Perm_merge_cancel_left_inv hP

  case res A _ _ _ 𝒟 _ _ _ _ _ _ hFu hFv _ ih =>
    simp only [HasBracket.brack] at ih
    have ⟨𝒥, hP⟩ := ih hl
    subst hl
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, huPf⟩ := hFu
    obtain ⟨hvx, hvPf⟩ := hFv
    exact HyperEnv.Perm.extract_one_res_source (A := Aᗮ)
      (by simp at hP ⊢ ; apply hP) hux hvx

  case perm hP _ ih =>
    simp at ih
    have ⟨𝒥, hP'⟩ := ih hl
    use 𝒥
    exact hP.symm.trans hP'

lemma TypingStepₘ_inv_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [x ∶ ⊥ :: Γᵣ] := by
  generalize hl : (x⸨⸩ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl

  case bot Γ _ _ _ _ _=>
    subst hl
    use ∅, Γ
    rw [HyperEnv.merge_unitL]

  case par₁ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP⟩ := ih hl
    expose_names
    use 𝒥 |ₕ ℋ, Γ'
    apply HyperEnv.Perm_rotate_rhs_right
    exact HyperEnv.Perm_merge_cancel_right_inv (hP.trans HyperEnv.Perm_merge_comm)

  case par₂ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP⟩ := ih hl
    expose_names
    use 𝒥 |ₕ 𝒢_1, Γ'
    apply HyperEnv.Perm_rotate_rhs_left
    rw [HyperEnv.merge_assoc]
    exact HyperEnv.Perm_merge_cancel_left_inv (hP.trans HyperEnv.Perm_merge_comm)

  case res A _ _ _ 𝒟 _ u v hu hv hneq hFu hFv _ ih =>
    simp only [HasParen.paren] at ih
    have ⟨𝒥, Γ', hP⟩ := ih hl
    subst hl
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, _⟩ := hFu
    obtain ⟨hvx, _⟩ := hFv
    have ⟨⟨hu𝒢, _, huΔ⟩, ⟨hv𝒢, hvΓ, _⟩⟩ := Typing_res_fresh (𝒟 u v hu hv hneq)
    exact HyperEnv.Perm.extract_bot_res_source (A := Aᗮ)
      (by simp at hP ⊢ ; apply hP) hux hvx hu𝒢 hv𝒢 hneq huΔ hvΓ

  case perm hP _ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP'⟩ := ih hl
    use 𝒥, Γ'
    exact hP.symm.trans hP'


lemma TypingStepₘ_inv_one_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, 𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by
  generalize hl : (x⟦()⟧ |ₗ y⸨()⸩) = l at hStep
  induction hStep <;> try simp at hl

  case par₁ ih =>
    expose_names
    obtain ⟨𝒢', Γ', hP'⟩ := ih hl
    use (𝒢' |ₕ ℋ), Γ'
    apply HyperEnv.Perm_rotate_rhs_right at hP'
    apply HyperEnv.Perm_rotate_rhs_left
    rw [← HyperEnv.merge_assoc]
    exact HyperEnv.Perm_merge_cancel_right_inv hP'

  case par₂ ih =>
    expose_names
    obtain ⟨ℋ', Γ', hP'⟩ := ih hl
    use (𝒢_1 |ₕ ℋ'), Γ'
    rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
    rw [HyperEnv.merge_assoc] at hP'
    exact HyperEnv.Perm_merge_cancel_left_inv hP'

  case syn 𝒥 𝒥' ℋ ℋ' Q Q' R R' l' l'' n' hD1 hD2 ℰ ℰ' ℱ ℱ' hSℰ hSℱ disj lwf ih1 ih2 =>
    rcases hl with ⟨rfl, rfl⟩
    obtain ⟨𝒥', hP𝒥⟩ := TypingStepₘ_inv_one_existential hSℰ
    obtain ⟨ℋ', Γ', hPℋ⟩ := TypingStepₘ_inv_bot_existential hSℱ
    use 𝒥' |ₕ ℋ', Γ'
    rw [HyperEnv.merge_assoc]
    apply HyperEnv.Perm.trans (HyperEnv.Perm.merge hP𝒥 hPℋ)
    repeat rw [HyperEnv.merge_assoc]
    apply HyperEnv.Perm_merge_cancel_left_inv
    conv_rhs => rw [← HyperEnv.merge_assoc]
    apply HyperEnv.Perm_rotate_rhs_left
    apply HyperEnv.Perm_merge_cancel_left_inv
    rw [List.append_eq, List.nil_append]
    apply HyperEnv.Perm_merge_singleton

  case res A _ l _ huinq _ u v hu hv hneq hFu hFv hStep ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP'⟩ := ih hl
    subst l
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, huy, huPf⟩ := hFu
    obtain ⟨hvx, hvy, hvPf⟩ := hFv
    have ⟨⟨hu𝒢, huΓ, huΔ⟩, ⟨hv𝒢, hvΓ, hvΔ⟩⟩ := Typing_res_fresh (huinq u v hu hv hneq)
    exact HyperEnv.Perm.extract_one_bot_res_source (A := Aᗮ)
      (by simp at ⊢ hP' ; exact hP') hux hvx huy hvy hu𝒢 hv𝒢 hneq hvΓ huΔ

  case perm hP _ ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP'⟩ := ih hl
    use 𝒢ᵣ, Γᵣ
    exact HyperEnv.Perm.trans hP.symm hP'

lemma TypingStepₘ_inv_one_bot {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  A = 1 ∧ B = ⊥ ∧ Γ = ∅ := by
  obtain ⟨𝒢ᵣ, Γᵣ, hP⟩ := TypingStepₘ_inv_one_bot_existential hStep
  have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
  have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟

  have hxLHS : [x ∶ 1] ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] := by
    have hxRHS : [x ∶ 1] ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP hxRHS
    simp [HasPerm.perm] at hPΞ
    subst hPΞ
    exact hΞ

  simp [HyperEnv.PairwiseDisjoint_merge] at hpw
  have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1

  have hyLHS : y ∶ ⊥ :: Δ ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] := by
    have hyRHS : (y ∶ ⊥ :: Γᵣ) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP hyRHS
    simp [HasPerm.perm] at hPΞ
    simp at hΞ
    rcases hΞ with h1 | h2 | h3
    · exfalso
      exact (HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ ⊥ h1)
        ((List.Perm.mem_iff (a := y ∶ ⊥) hPΞ.symm).mp (by simp))
    · subst h2
      have hyin := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      simp at hyin
      rcases hyin with ⟨rfl, rfl⟩ | h
      · exfalso ; simp at hDΓΔ
      · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
    · subst h3
      have hyin := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      simp at hyin
      rcases hyin with rfl | h
      · simp
      · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ h)

  simp at hxLHS hyLHS
  rcases hxLHS with h1 | h2 | h3
  · exfalso
    apply HyperEnv.not_mem_names_iff.mp hx𝒢 [x ∶ 1] 1 h1
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  · rcases h2 with ⟨rfl, rfl⟩
    · rcases hyLHS with h4 | h5 | h6
      · exfalso
        apply HyperEnv.not_mem_names_iff.mp hy𝒢 (y ∶ ⊥ :: Δ) ⊥ h4
        simp only [List.mem_cons, true_or]
      · obtain ⟨⟨rfl, _⟩, _⟩ := h5
        simp at hDΓΔ
      · subst h6 ; simp
  · obtain ⟨⟨rfl, _⟩, _⟩ := h3
    simp at hDΓΔ

lemma HyperEnv.rename_res_left
  {ℋ : HyperEnv} {Γ Δ : Env} {x z w : FPName} {A B : Types}
  (hxℋ : x ∉ ℋ.names) (hxΓ : x ∉ Γ.names) (hxΔ : x ∉ Δ.names) (hxw : x ≠ w) :
  ∀ Ξ ∈ ℋ |ₕ [z ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (x, C) ∈ Ξ → x = z := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hxℋ (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · rfl
    · exfalso
      exact hxΓ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exfalso
      exact hxw rfl
    · exfalso
      exact hxΔ (Env.mem_pair_fst_in_names _ h)

lemma HyperEnv.rename_res_right
  {ℋ : HyperEnv} {Γ Δ : Env} {x y w : FPName} {A B : Types}
  (hyℋ : y ∉ ℋ.names) (hyΓ : y ∉ Γ.names) (hyΔ : y ∉ Δ.names) (hyx : y ≠ x) :
  ∀ Ξ ∈ ℋ |ₕ [x ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (y, C) ∈ Ξ → y = w := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hyℋ (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exfalso
      exact hyx rfl
    · exfalso
      exact hyΓ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · rfl
    · exfalso
      exact hyΔ (Env.mem_pair_fst_in_names _ h)




theorem typability_subject_reductionₘ
  {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
  (𝒟 : Typing n P 𝒢) (hPS : ProcStepₘ P l P') :
  ∃ (𝒢' : HyperEnv) (𝒟' : Typing n P' 𝒢'),
    TypingStepₘ 𝒟 l 𝒟' := by
  induction hPS generalizing n 𝒢

  case one =>
    obtain ⟨hP, 𝒟'⟩ := Typing_inv_one 𝒟
    have ⟨Δ, heq, hPΔ⟩:= HyperEnv.Perm_singleton_inv hP.symm
    simp only [HasPerm.perm, List.singleton_perm] at hPΔ
    subst hPΔ heq
    use ∅, 𝒟'
    apply TypingStepₘ.one

  case bot =>
    obtain ⟨Γ, hP, 𝒟'⟩ := Typing_inv_bot 𝒟
    have := HyperEnv.Nodup_perm hP (Typing_preserves_linearity 𝒟).1
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons] at this
    obtain ⟨hxΓ, _⟩ := this
    use [Γ], 𝒟'
    exact TypingStepₘ.perm hP.symm (TypingStepₘ.bot (hF := hxΓ))

  case tensor Q x y hF =>
    obtain ⟨A, B, Γ, Δ, L, hP, 𝒟'⟩ := Typing_inv_tensor 𝒟
    simp [← ne_eq] at hF
    obtain ⟨hF1, hF2⟩ := hF

    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ Q.f)
    simp [← ne_eq] at hz
    obtain ⟨hzy, hz, hfz⟩ := hz
    have 𝒟z := (𝒟' z hz)
    have hfy := Proc.not_mem_f_open hzy hfz hF2
    rw [(Typing.f_eq_names 𝒟z)] at hfy

    have ⟨hyΓ, hyΔ⟩ : y ∉ Γ.names ∧ y ∉ Δ.names := by
      constructor <;> (intro hc ; simp [hc] at hfy)

    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names ∪ Δ.names := by
      simp [hF2, hyΓ, hyΔ, hF1]

    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons, Env.names_merge,
      Finset.mem_union, not_or] at hnd'

    have 𝒟y := Typing_tensor_all_fresh 𝒟' y hy
    · use [y ∶ A :: Γ] |ₕ [x ∶ B :: Δ], 𝒟y
      apply TypingStepₘ.perm hP.symm
      apply TypingStepₘ.tensor
      · exact hnd'.1
      · exact 𝒟'
      · exact hy

  case parr Q x y hF =>
    obtain ⟨A, B, Γ, L, hP, 𝒟'⟩ := Typing_inv_parr 𝒟
    simp [← ne_eq] at hF
    obtain ⟨hF1, hF2⟩ := hF

    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ Q.f)
    simp [← ne_eq] at hz
    obtain ⟨hzy, hz, hfz⟩ := hz
    have 𝒟z := (𝒟' z hz)
    have hfy := Proc.not_mem_f_open hzy hfz hF2
    rw [(Typing.f_eq_names 𝒟z)] at hfy

    have hyΓ : y ∉ Γ.names := by
      intro hc ; simp [hc] at hfy

    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names := by
      simp [hF2, hyΓ, hF1]

    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd'

    have 𝒟y := Typing_parr_all_fresh 𝒟' y hy
    · use [y ∶ A :: x ∶ B :: Γ], 𝒟y
      apply TypingStepₘ.perm hP.symm
      apply TypingStepₘ.parr
      · exact hnd'.1
      · exact 𝒟'
      · exact hy

  case par₁ disj ih =>
    have ⟨𝒥, 𝒦, hP, hTQ, hTR, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTQ', hStepQQ'⟩ := ih hTQ
    have hD' : Disjoint 𝒥'.names 𝒦.names :=
      TypingStepₘ_par_preserves_disjoint hTR hStepQQ' hD disj
    use 𝒥' |ₕ 𝒦, (Typing.mix hD' hTQ' hTR)
    apply TypingStepₘ.perm hP.symm
    · apply TypingStepₘ.par₁ hStepQQ' disj
      · exact hD
      · exact hD'
      · exact hTR

  case par₂ disj ih =>
    have ⟨𝒦, 𝒥, hP, hTR, hTQ, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTQ', hStepQQ'⟩ := ih hTQ
    have hD' : Disjoint 𝒦.names 𝒥'.names :=
      (TypingStepₘ_par_preserves_disjoint hTR hStepQQ' hD.symm disj).symm
    use 𝒦 |ₕ 𝒥', (Typing.mix hD' hTR hTQ')
    apply TypingStepₘ.perm hP.symm
    · apply TypingStepₘ.par₂ hStepQQ' disj
      · exact hD
      · exact hD'
      · exact hTR

  case syn l' l'' _ _ disj lwf ih1 ih2 =>
    have ⟨𝒥, 𝒦, hP, hTR, hTQ, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTR', hStepRR'⟩ := ih1 hTR
    have ⟨𝒦', hTQ', hStepQQ'⟩ := ih2 hTQ
    have hD' : 𝒥'.disjoint 𝒦' :=
      TypingStepₘ_syn_preserves_disjoint hStepRR' hStepQQ' hD disj lwf
    use 𝒥' |ₕ 𝒦', (Typing.mix ?_ hTR' hTQ')
    · apply TypingStepₘ.perm hP.symm
      · apply TypingStepₘ.syn
        · exact hD
        · exact hD'
        · exact hStepRR'
        · exact hStepQQ'
        · exact disj
        · exact lwf
      · exact hD'

  case one_bot Q Q' x y hxQf hyQf hxy hPS ih =>
    expose_names
    have ⟨A, Γ, Δ, ℋ, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    have hNames := Typing.f_eq_names 𝒟
    simp [HyperEnv.names_eq_of_perm hP] at hNames
    simp [hNames, -Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff] at hxQf hyQf
    obtain ⟨hxℋ, hxΓ, hxΔ⟩ := hxQf
    obtain ⟨hyℋ, hyΓ, hyΔ⟩ := hyQf
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      exists_two_fresh (L ∪ Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names ∪ {x, y})
    simp [← ne_eq, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at hz hw
    obtain ⟨hzx, hzy, hzL, hzQf, hzℋ, hzΓ, hzΔ⟩ := hz
    obtain ⟨hwx, hwy, hwL, hwQf, hwℋ, hwΓ, hwΔ⟩ := hw

    have 𝒟zw := 𝒟' z hzL w hwL hzw
    have 𝒟xw := Typing_substNames 𝒟zw (x := z) (y := x)
      (HyperEnv.rename_res_left hxℋ hxΓ hxΔ hwx.symm)

    simp only [HyperEnv.substNames_merge, HyperEnv.substNames_distributes,
      Env.substNames_distributes, FPName.subst_self, HyperEnv.names_nil,
      Finset.notMem_empty, not_false_eq_true, HyperEnv.substNames_of_not_mem] at 𝒟xw

    rw [HyperEnv.substNames_of_not_mem hzℋ, Env.substNames_of_not_mem hzΓ,
        Env.substNames_of_not_mem hzΔ, FPName.subst_self_of_ne hzw.symm,
        Proc.open_two_substNames, Proc.substNames_of_not_mem hzQf,
        FPName.subst_self, FPName.subst_self_of_ne hzw.symm] at 𝒟xw

    have 𝒟xy := Typing_substNames 𝒟xw (x := w) (y := y)
      (HyperEnv.rename_res_right hyℋ hyΓ hyΔ hxy.symm)

  case tensor_parr L _ ih =>
    sorry

  case res =>
    have ⟨A, Γ, Δ, 𝒢, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟

    sorry





































/-
  Together session_fidelity_procₘ and typability_subject_reductionₘ establishes the Strong
  Bisimulation required by Theorem 4.7.
-/

/- NOTE FOR PAPER
The res rule in fig 5 and the res rule in fig 2, has swapped which name is typed with Aᗮ, visually
this could induce some confusion, but theoretically it shoulnd't have any impact.(since to make them
match again one could just pass Aᗮ as the type to either in which case the ordering would swap.)
-/

-- TODO: Prove Session fidelity, erasure, type preservation, Session fidelity for πLL
