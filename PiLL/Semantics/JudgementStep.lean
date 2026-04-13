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

  case res 𝒢' _ Γ' _ Δ' _ _ _ _ _ _ _ huniq' x y hx hy hneq hFx hFy hStep ih =>
    intro a ha
    simp only [HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge, HyperEnv.names_nil,
      Finset.union_empty, Finset.mem_union, List.append_assoc, List.cons_append,
      List.nil_append, Env.names_distributes, Finset.singleton_union, Finset.union_insert,
      Finset.insert_union, Finset.union_assoc] at ha ih ⊢
    have haLHS : a ∈ insert y (insert x (𝒢'.names ∪ (Γ'.names ∪ Δ'.names))) := by
      simp only [Finset.mem_insert, Finset.mem_union, ha, or_true]
    have haRHS := ih haLHS
    simp only [Finset.mem_insert, Finset.mem_union] at haRHS

    have ⟨hnd, hpw⟩ := Typing_preserves_linearity (huniq' x y hx hy hneq)
    simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd
    rw [HyperEnv.merge_assoc] at hpw
    have hD := HyperEnv.PairwiseDisjoint_tail_not_in_head hpw
    simp at hD





    rcases haRHS with rfl | rfl | h
    · rcases ha with h1 | h2 | h3
      · exfalso ; apply hnd.2.1 ; sorry -- continue with hpw disjointness
      · sorry
      · sorry
    · sorry -- same as above
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

  case one_bot L _ ih =>
    sorry

  case tensor_parr L _ ih =>
    sorry

  case res =>
    sorry





























  all_goals sorry








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
