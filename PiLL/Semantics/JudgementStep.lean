import PiLL.Substitution
import PiLL.Semantics.Labels

-- Same reason as in Environment.lean
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

macro "distribute_names " T:ident : tactic =>
  `(tactic|
      simp only [HyperEnv.substNames_merge, HyperEnv.substNames_distributes,
        Env.substNames_distributes, FPName.subst_self, HyperEnv.names_nil,
        Finset.notMem_empty, not_false_eq_true, HyperEnv.substNames_of_not_mem] at $T:ident
    )

macro "clean_subst " T:ident h1:ident h2:ident h3:ident h4:ident h5:ident : tactic =>
  `(tactic|
      simp only [HyperEnv.substNames_of_not_mem $h1, Env.substNames_of_not_mem $h2,
        Env.substNames_of_not_mem $h3, Env.substNames_empty, Proc.open_two_substNames,
        Proc.substNames_of_not_mem $h4, FPName.subst_self, Env.substNames_nil,
        FPName.subst_self_of_ne $h5] at $T:ident
    )

macro "clean_substNames "
  T:ident h𝒢:ident hΓ:ident hΔ:ident hfpn:ident hpf:ident : tactic =>
  `(tactic|
      distribute_names $T <;>
      clean_subst $T $h𝒢 $hΓ $hΔ $hpf $hfpn
    )



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

lemma Typing_one_bot_all_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv} {Γ : Env}
  {L : Finset FPName}
  (huniq : ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
    Typing n (P⸨#z, #w⸩) (𝒢 |ₕ [z ∶ 1 :: ∅] |ₕ [w ∶ ⊥ :: Γ])) :
  ∀ x y,
  x ∉ ({y} ∪ P.f ∪ 𝒢.names ∪ Γ.names) →
  y ∉ (P.f ∪ 𝒢.names ∪ Γ.names) →
  Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ 1 :: ∅] |ₕ [y ∶ ⊥ :: Γ]) := by
  intros x y hFx hFy
  obtain ⟨z, w, hz, hw, hzw⟩ := exists_two_fresh (L ∪ {x, y} ∪ 𝒢.names ∪ Γ.names ∪ P.f)
  simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq] at hFx hFy hz hw
  obtain ⟨hzL, hzx, hzy, hz𝒢, hzΓ, hzPf⟩ := hz
  obtain ⟨hwL, hwx, hwy, hw𝒢, hwΓ, hwPf⟩ := hw
  obtain ⟨hxy, hxPf, hx𝒢, hxΓ⟩ := hFx
  obtain ⟨hyPf, hy𝒢, hyΓ⟩ := hFy
  have 𝒟zw := huniq z hzL w hwL hzw
  have 𝒟xw := Typing_substNames (x := z) (y := x) 𝒟zw
    (HyperEnv.substNames_res_left (Γ := ∅) (Δ := Γ) hx𝒢 (by simp) hxΓ hwx.symm)
  clean_substNames 𝒟xw hz𝒢 hzΓ hzΓ hzw.symm hzPf
  have 𝒟xy := Typing_substNames (x := w) (y := y) 𝒟xw
    (HyperEnv.substNames_res_right (Γ := ∅) (Δ := Γ) hy𝒢 (by simp) hyΓ hxy.symm)
  clean_substNames 𝒟xy hw𝒢 hwΓ hwΓ hwx.symm hwPf
  exact 𝒟xy

lemma Typing_res_all_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env} {A B : Types}
  {L : Finset FPName}
  (huniq : ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
    Typing n (P⸨#z, #w⸩) (𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ B :: Δ])) :
  ∀ x y,
  x ∉ ({y} ∪ P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names) →
  y ∉ (P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names) →
  Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ]) := by
  intros x y hFx hFy
  obtain ⟨z, w, hz, hw, hzw⟩ :=
    exists_two_fresh (L ∪ {x, y} ∪ 𝒢.names ∪ Γ.names ∪ Δ.names ∪ P.f)
  simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq] at hFx hFy hz hw
  obtain ⟨hzL, hzx, hzy, hz𝒢, hzΓ, hzΔ, hzPf⟩ := hz
  obtain ⟨hwL, hwx, hwy, hw𝒢, hwΓ, hwΔ, hwPf⟩ := hw
  obtain ⟨hxy, hxPf, hx𝒢, hxΓ, hxΔ⟩ := hFx
  obtain ⟨hyPf, hy𝒢, hyΓ, hyΔ⟩ := hFy
  have 𝒟zw := huniq z hzL w hwL hzw
  have 𝒟xw := Typing_substNames (x := z) (y := x) 𝒟zw
    (HyperEnv.substNames_res_left (Γ := Γ) (Δ := Δ) hx𝒢 hxΓ hxΔ hwx.symm)
  clean_substNames 𝒟xw hz𝒢 hzΓ hzΔ hzw.symm hzPf
  have 𝒟xy := Typing_substNames (x := w) (y := y) 𝒟xw
    (HyperEnv.substNames_res_right (Γ := Γ) (Δ := Δ) hy𝒢 hyΓ hyΔ hxy.symm)
  clean_substNames 𝒟xy hw𝒢 hwΓ hwΔ hwx.symm hwPf
  exact 𝒟xy





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
      {𝒢 𝒢' : HyperEnv} {Γ : Env} {P P' : Proc} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
        Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ 1 :: ∅] |ₕ [y ∶ ⊥ :: Γ])}
      {x y : FPName}
      {hx : x ∉ ({y} ∪ P.f ∪ 𝒢.names ∪ Γ.names)}
      {hy : y ∉ (P.f ∪ 𝒢.names ∪ Γ.names)}
      -- {𝒟' : Typing n P' 𝒢'}                          -- FIXME: explain why this
      {𝒟' : Typing n P' (𝒢 |ₕ [∅‚ Γ])}            -- and not this in the report
      (hStep : TypingStepₘ (Typing_one_bot_all_fresh huniq x y hx hy) (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

| tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {A B : Types} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
                Typing n
                  (P⸨#x, #y⸩)
                  (𝒢 |ₕ [x ∶ A ⨂ B :: Env.merge Γ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])}
      {huniq' : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
                ∀ x' ∉ L, ∀ y' ∉ L, x' ≠ y' →
                x ≠ x' → x ≠ y' → y ≠ x' → y ≠ y' →
                Typing n
                  (P'⸨#x, #y⸩⸨#x', #y'⸩)
                  (𝒢 |ₕ [x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ])}
      {𝒟' : Typing n (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P')) (𝒢 |ₕ [Env.merge (Env.merge Γ Δ) Ξ])}
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      {x' y' : FPName} (hx' : x' ∉ L) (hy' : y' ∉ L) (hneq' : x' ≠ y')
      (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x') (hyy' : y ≠ y')
      (hxP : x ∉ P.f) (hyP : y ∉ P.f) (hx'P : x' ∉ P.f) (hy'P : y' ∉ P.f)
      (hStep : TypingStepₘ (huniq x hx y hy hneq) (x⟦x'⟧ |ₗ y⸨y'⸩)
                (huniq' x hx y hy hneq x' hx' y' hy' hneq' hxx' hxy' hyx' hyy')) :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

| res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {A : Types} {n : Nat} {l : Lbl}
      {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
                Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])}
      {huniq' : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
                Typing n (P'⸨#x, #y⸩) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'])}
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      (hFx : x ∉ P.f ∪ l.f ∪ l.i) (hFy : y ∉ P.f ∪ l.f ∪ l.i)
      (hStep : TypingStepₘ (huniq x hx y hy hneq) l (huniq' x hx y hy hneq)) :
      TypingStepₘ (Typing.cut L huniq) l (Typing.cut L huniq')

  ------- Additional Structural / Exchange Rules -------

  | perm {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' : Proc} {n n' : Nat} {l : Lbl}
    {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ ℋ} (hP1 : 𝒢 ~ 𝒢') (hP2 : ℋ ~ ℋ')
    (hTS : TypingStepₘ 𝒟 l 𝒟') :
    TypingStepₘ (Typing.exchange_hyper 𝒟 hP1) l (Typing.exchange_hyper 𝒟' hP2)

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
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A : Types} {l : Lbl}
      (hFx : x ∉ l.i ∪ l.f) (hFy : y ∉ l.i ∪ l.f) :
      EnvStepₘ (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) (l) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])

  ------- Additional Structural / Exchange Rules -------

  | perm {𝒢 𝒢' ℋ ℋ' : HyperEnv} {l : Lbl} (hP1 : 𝒢 ~ 𝒢') (hP2 : ℋ ~ ℋ') :
      (hES : EnvStepₘ 𝒢 l ℋ) →
      -------------------------
      EnvStepₘ 𝒢' l ℋ'

instance : HasStep HyperEnv Lbl HyperEnv where step := EnvStepₘ









lemma EnvStep_inv_one_existential {𝒢 𝒢' : HyperEnv} {x : FPName}
  (hES : EnvStepₘ 𝒢 (x⟦⟧) 𝒢') :
  ∃ 𝒢_rest, (𝒢 ~ 𝒢_rest |ₕ [[x ∶ 1]]) ∧ (𝒢' ~ 𝒢_rest) := by
  generalize hl : (x⟦⟧ : Lbl) = l at hES
  induction hES <;> try contradiction
  all_goals
    simp only [HasBracket.brack, HasParen.paren, Lbl.act.injEq,
      reduceCtorEq, Act.one.injEq] at hl
  case one =>
    use ∅
    subst hl
    simp only [List.empty_eq, List.nil_append, HyperEnv.Perm_refl, and_self]
  case par₁ 𝒥  _ _ ih =>
    obtain ⟨𝒢ᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hl
    use (𝒢ᵣ_ih |ₕ 𝒥)
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm.merge
      · apply HyperEnv.Perm_exchange_rhs
        · exact HyperEnv.Perm.merge_comm
        · exact h_pre_ih
      · rfl
    · exact HyperEnv.Perm.merge h_post_ih (by rfl)
  case par₂ 𝒥  _ _ _ _ ih =>
    obtain ⟨ℋᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hl
    use (𝒥 |ₕ ℋᵣ_ih)
    constructor
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm.merge (by rfl) h_pre_ih
    · exact HyperEnv.Perm.merge (by rfl) h_post_ih
  case res ℋ ℋ' Γ Γ' Δ Δ' u v A l' hFu hFv hES ih =>

    have hxu : x ≠ u := by sorry
    have huℋ : u ∉ ℋ.names := by sorry
    have huΔ : u ∉ Δ.names := by sorry
    have hxv : x ≠ v := by sorry
    have hvℋ : v ∉ ℋ.names := by sorry
    have hvΓ : v ∉ Γ.names := by sorry
    have huv : u ≠ v := by sorry

    obtain ⟨𝒢ᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hl
    apply HyperEnv.Perm.extract_one_res
      h_pre_ih h_post_ih hxu hxv huℋ hvℋ huv huΔ hvΓ

  case perm hP hP' _ ih =>
    obtain ⟨𝒥, h_pre_ih, h_post_ih⟩ := ih hl
    use 𝒥
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP) h_pre_ih
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP') h_post_ih



lemma EnvStep_inv_bot_existential {𝒢 𝒢' : HyperEnv} {y : FPName}
  (hES : 𝒢 -[(y⸨⸩ : Lbl)]-> 𝒢') :
  ∃ 𝒢ᵣ Γ, (𝒢 ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Γ]) ∧ (𝒢' ~ 𝒢ᵣ |ₕ [Γ]) := by
  generalize hl : (y⸨⸩ : Lbl) = l at hES
  induction hES
  case bot Γ _ =>
    simp only [HasParen.paren, Lbl.act.injEq, Act.bot.injEq] at hl
    subst hl
    use ∅, Γ
    simp
  case par₁ ℋ ℋ' 𝒥 l hES ih =>
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hl
    use (𝒢ᵣ_ih |ₕ 𝒥), Γ_ih
    constructor
    · have h1 := HyperEnv.Perm.merge_right h_pre_ih 𝒥
      have h2 : 𝒢ᵣ_ih |ₕ [y ∶ ⊥ :: Γ_ih] |ₕ 𝒥 ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [y ∶ ⊥ :: Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.merge_comm
      exact HyperEnv.Perm.trans h1 h2
    · have h1 := HyperEnv.Perm.merge_right h_post_ih 𝒥
      have h2 : 𝒢ᵣ_ih |ₕ [Γ_ih] |ₕ 𝒥 ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.merge_comm
      exact h1.trans h2
  case par₂ 𝒥 ℋ ℋ' l hES ih =>
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hl
    use (𝒢ᵣ_ih |ₕ 𝒥), Γ_ih
    constructor
    · have h1 := HyperEnv.Perm.merge_left h_pre_ih 𝒥
      have h2 : 𝒥 |ₕ (𝒢ᵣ_ih |ₕ [y ∶ ⊥ :: Γ_ih]) ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [y ∶ ⊥ :: Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_assoc
      exact h1.trans h2
    · have h1 := HyperEnv.Perm.merge_left h_post_ih 𝒥
      have h2 : 𝒥 |ₕ (𝒢ᵣ_ih |ₕ [Γ_ih]) ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_assoc
      exact h1.trans h2
  case res 𝒢 ℋ Γ Γ' Δ Δ' u v A  l hES ih =>
    sorry -- FIXME:
    -- exact HyperEnv.Perm.extract_bot_res
      -- h_pre_ih h_post_ih hFlu hFlv hFu.1 hFv.1 hFu'.1 hFv'.1 hneq hFu.2.2 hFv.2.1
  case perm hP hP' _ ih =>
    obtain ⟨𝒥, Γ, h_pre_ih, h_post_ih⟩ := ih hl
    use 𝒥, Γ
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP) h_pre_ih
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP') h_post_ih
  all_goals
    simp only [HasParen.paren, HasBracket.brack, Lbl.act.injEq, reduceCtorEq] at hl

lemma EnvStep_inv_one_bot_existential {𝒢 ℋ : HyperEnv} {x y : FPName}
  (hES : 𝒢 -[x⟦⟧ |ₗ y⸨⸩]-> ℋ) :
  ∃ 𝒢' Γ,
    (𝒢 ~ 𝒢' |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) ∧
    (ℋ ~ 𝒢' |ₕ [Γ]) := by
  generalize hl : (x⟦⟧ |ₗ y⸨⸩) = lbl at hES
  induction hES <;> try contradiction
  all_goals
    simp only [HasBracket.brack, HasParen.paren, Lbl.par.injEq] at hl
  case par₁ 𝒥 _ hFl ih =>
    obtain ⟨𝒢ᵣ, Γₙ, h_pre_ih, h_post_ih⟩ := ih hl
    refine ⟨𝒥 |ₕ 𝒢ᵣ, Γₙ, ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm.merge
      · rw [← HyperEnv.merge_assoc]
        exact h_pre_ih
      · rfl
    · apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm.merge
      · exact h_post_ih
      · rfl
  case par₂ 𝒥 _ _ _  hFl ih =>
    obtain ⟨ℋᵣ, Γₙ, h_pre_ih, h_post_ih⟩ := ih hl
    refine ⟨𝒥 |ₕ ℋᵣ, Γₙ, ?_, ?_⟩
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge
      · rfl
      · rw [← HyperEnv.merge_assoc]
        exact h_pre_ih
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge
      · rfl
      · exact h_post_ih
  case syn hES𝒢 hESℋ ih𝒢 ihℋ =>
    obtain ⟨hlx, hly⟩ := hl
    obtain ⟨𝒢_rest1, h_pre1, h_post1⟩ := EnvStep_inv_one_existential (hlx ▸ hES𝒢)
    obtain ⟨𝒢_rest2, Γₙ, h_pre2, h_post2⟩ := EnvStep_inv_bot_existential (hly ▸ hESℋ)
    refine ⟨𝒢_rest1 |ₕ 𝒢_rest2, Γₙ, ?_, ?_⟩
    · have := h_pre1.merge h_pre2
      apply HyperEnv.Perm_pull_rhs_mid_left at this
      rw [HyperEnv.merge_assoc] at this
      apply HyperEnv.Perm_pull_rhs_mid_left at this
      simp only [← HyperEnv.merge_assoc] at this
      exact this
    · rw [HyperEnv.merge_assoc]
      exact h_post1.merge h_post2



  case res 𝒥 𝒥' Γ Γ' Δ Δ' u v A l hFu hFv hES ih =>

    have hxu : x ≠ u := by sorry
    have hyu : y ≠ u := by sorry
    have hu𝒥 : u ∉ 𝒥.names := by sorry
    have hu𝒥' : u ∉ 𝒥'.names := by sorry
    have huΓ : u ∉ Γ.names := by sorry
    have huΔ : u ∉ Δ.names := by sorry
    have hxv : x ≠ v := by sorry
    have hyv : y ≠ v := by sorry
    have hv𝒥 : v ∉ 𝒥.names := by sorry
    have hv𝒥' : v ∉ 𝒥'.names := by sorry
    have hvΓ : v ∉ Γ.names := by sorry
    have hvΔ : v ∉ Δ.names := by sorry
    have huv : u ≠ v := by sorry


    have ⟨ℋ, Ξ, hP_ih_pre, hP_ih_post⟩ := ih hl
    apply HyperEnv.Perm.extract_one_bot_res
      hP_ih_pre hP_ih_post hxu hxv hyu hyv hu𝒥 hv𝒥 hu𝒥' hv𝒥' huv hvΓ huΔ

  case perm hP hP' _ ih =>
    obtain ⟨𝒢ᵣ, Γₙ, h_pre_ih, h_post_ih⟩:= ih hl
    use 𝒢ᵣ, Γₙ
    constructor
    · exact hP.symm.trans h_pre_ih
    · exact hP'.symm.trans h_post_ih











#check HyperEnv.Perm.extract_one_res
#check HyperEnv.Perm.extract_bot_res
#check HyperEnv.Perm.extract_one_bot_res

lemma HyperEnv.Perm.cancel_one_bot {𝒢 ℋ : HyperEnv} {Γ Γ' : Env} {x y : FPName}
  (hx𝒢 : x ∉ 𝒢.names) (hy𝒢 : y ∉ 𝒢.names) (hyΓ : y ∉ Γ.names)
  (hP : ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ] ~ 𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ']) :
  ℋ ~ 𝒢 ∧ Γ ~ Γ' := by
  have hxin : [x ∶ 1] ∈ ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ] := by simp
  obtain ⟨Ex, hEx, hPEx⟩ := HyperEnv.Perm_mem hP.symm hxin
  have hyin : (y ∶ ⊥ :: Γ) ∈ ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ] := by simp
  obtain ⟨Ey, hEy, hPEy⟩ := HyperEnv.Perm_mem hP.symm hyin
  simp only [List.mem_append, List.mem_singleton] at hEx hEy
  rcases hEx with h | rfl | rfl
  · rcases h with h1 | rfl
    · exfalso
      simp [HasPerm.perm] at hPEx
      subst hPEx
      have ⟨A, hin⟩ := (Env.mem_pair_fst_in_names_iff (x := x) (Γ := [x ∶ 1])).mp (by simp)
      exact hx𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
    · rcases hEy with h1 | rfl | rfl
      · rcases h1 with h𝒢 | rfl
        · have ⟨A, hin⟩ := (Env.mem_pair_fst_in_names_iff (x := y) (Γ := (y ∶ ⊥ :: Γ))).mp (by simp)
          have hinEy := (List.Perm.mem_iff (a := y ∶ A) hPEy).mpr hin
          have hin𝒢ᵣ:= (HyperEnv.mem_of_mem_mem_names hinEy h𝒢)
          simp at hin
          rcases hin with rfl | h
          · exfalso ; exact (hy𝒢) hin𝒢ᵣ
          · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
        · simp [HasPerm.perm] at hPEy
      · constructor
        · have hP1 : 𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ'] ~  𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ] := by
            apply HyperEnv.Perm_merge_cancel_left_inv
            exact HyperEnv.Perm_singleton_singleton.mpr hPEy
          exact HyperEnv.Perm_merge_cancel_right
            (HyperEnv.Perm_merge_cancel_right (hP.trans hP1))
        · simp [HasPerm.perm, List.perm_cons] at hPEy ⊢
          exact hPEy.symm
  · simp [HasPerm.perm] at hPEx


lemma EnvStep_inv_one_bot {𝒢 𝒢' : HyperEnv} {Γ : Env} {x y : FPName}
  (hx𝒢 : x ∉ 𝒢.names) (hy𝒢 : y ∉ 𝒢.names) (hyΓ : y ∉ Γ.names)
  (hES : EnvStepₘ (𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) (x⟦()⟧ |ₗ y⸨()⸩) 𝒢') :
  𝒢' ~ 𝒢 |ₕ [∅‚ Γ] := by

  have ⟨ℋ, Ξ, hP1, hP2⟩ := EnvStep_inv_one_bot_existential hES -- FIXME:


  have hNames: 𝒢.names = ℋ.names := by
    have hx_rhs : ([x ∶ 1]) ∈ ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
    have hy_rhs : (y ∶ ⊥ :: Ξ) ∈ ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
    obtain ⟨Ex, hEx_lhs, hPEx⟩ := HyperEnv.Perm_mem hP1 hx_rhs
    obtain ⟨Ey, hEy_lhs, hPEy⟩ := HyperEnv.Perm_mem hP1 hy_rhs
    simp only [List.mem_append, List.mem_singleton] at hEx_lhs hEy_lhs
    rcases hEx_lhs with h𝒢 | rfl | rfl
    · simp [HasPerm.perm] at hPEx
      subst hPEx
      rcases h𝒢 with h1 | h2
      · exfalso
        have : x ∈ Env.names [x ∶ 1] := by simp
        have ⟨A, hin⟩ := Env.mem_pair_fst_in_names_iff.mp this
        have := HyperEnv.mem_of_mem_mem_names hin h1
        exact hx𝒢 this
      · rcases hEy_lhs with h𝒢 | rfl
        · rcases h𝒢 with h | rfl
          · exfalso
            have hyinEy : y ∈ Env.names (y ∶ ⊥ :: Ξ) := by simp
            have ⟨A, hin⟩ := Env.mem_pair_fst_in_names_iff.mp hyinEy
            have hy𝒢' := HyperEnv.mem_of_mem_mem_names ((List.Perm.mem_iff hPEy).mpr hin) h
            exact hy𝒢 hy𝒢'
          · simp [HasPerm.perm] at hPEy
        · have hP3 : 𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ] ~  𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by
            apply HyperEnv.Perm_merge_cancel_left_inv
            exact HyperEnv.Perm_singleton_singleton.mpr hPEy
          have hP4 := hP3.symm.trans hP1
          exact HyperEnv.names_eq_of_perm (HyperEnv.Perm_merge_cancel_right
            (HyperEnv.Perm_merge_cancel_right hP4))
    · simp [HasPerm.perm] at hPEx

  have hxℋ : x ∉ ℋ.names := by simp [← hNames, hx𝒢]
  have hyℋ : y ∉ ℋ.names := by simp [← hNames, hy𝒢]

  apply HyperEnv.Perm.cancel_one_bot at hP1
  · apply hP2.trans
    apply hP1.1.symm.merge (HyperEnv.Perm_singleton_singleton.mpr hP1.2).symm
  · exact hxℋ
  · exact hyℋ
  · exact hyΓ





























-- FIXME: Move to Environment
lemma Env.cons_nil' {x : FPName} {A : Types} : x ∶ A :: ∅ = [x ∶ A] := by simp

lemma Env.cons_empty' {x : FPName} {A : Types} : x ∶ A :: [] = [x ∶ A] := by simp


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

  case one_bot ℋ ℋ' Γ Q Q' m L huniq x y hFx hFy ℰ hTS ih =>

    have hxℋ : x ∉ ℋ.names := by sorry
    have hyℋ : y ∉ ℋ.names := by sorry
    have hyΓ : y ∉ Γ.names := by sorry
    have hxy : x ≠ y := by sorry



    have hP:= EnvStep_inv_one_bot hxℋ hyℋ hyΓ ih
    apply EnvStepₘ.perm (by rfl) hP.symm
    apply EnvStepₘ.one_bot (x := x) (y := y)
    exact EnvStepₘ.perm (by rfl) hP ih







  case tensor_parr ih =>
    exact EnvStepₘ.tensor_parr ih

  case res hFx hFy _ ih =>
    apply EnvStepₘ.res ?_ ?_ ih
    all_goals
      simp only [Finset.mem_union, not_or, Finset.union_assoc] at hFx hFy ⊢
    · exact ⟨hFx.2.2, hFx.2.1⟩
    · exact ⟨hFy.2.2, hFy.2.1⟩

  case perm hP hP' hTS ih => exact EnvStepₘ.perm hP hP' ih

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

  case one_bot ℋ Γ Q Q' m L huniq x y hx hy 𝒟'' hSP ih =>
    simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Finset.mem_union, not_or, ← ne_eq] at hx hy
    obtain ⟨hxy, hxQf, hxℋ, hxΓ⟩ := hx
    obtain ⟨hyQf, hyℋ, hyΓ⟩ := hy
    exact ProcStepₘ.one_bot hxQf hyQf hxy ih

  case tensor_parr hxy _ _ _ _ hx'y' hxx' hxy' hyx' hyy' hxP hyP hx'P hy'P _ ih =>
    exact ProcStepₘ.tensor_parr hxP hx'P hyP hy'P hxx' hxy hxy' hyx' hyy' hx'y' ih

  case res hneq hFx hFy _ ih =>
    exact ProcStepₘ.res hFx hFy hneq ih

  case perm hP hTS ih => exact ih

lemma TypingStepₘ_names_bound {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv} {l : Lbl}
  {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 l 𝒟') :
  𝒢'.names ⊆ 𝒢.names ∪ l.i := by
  induction hStep

  case one | bot | tensor | parr | tensor_parr | one_bot => simp

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

-- NOTE: For generalized target env in TypingStep's one_bot rule
  -- case one_bot ℋ ℋ' Γ Q Q' m l' huniq x y hx hy 𝒟'' hStep ih =>
  --   have hEnvStep := session_fidelity_envₘ hStep
  --   have ⟨H, E, hP𝒟, hP𝒟'⟩ := EnvStep_inv_one_bot_existential hEnvStep -- FIXME: if uncommented
  --   simp only [env] at hP𝒟 hP𝒟'
  --   have hNamesEq := HyperEnv.names_eq_of_perm hP𝒟
  --   have hNamesEq' := HyperEnv.names_eq_of_perm hP𝒟'
  --   simp
  --   intro w hw
  --   have 𝒟xy := Typing_one_bot_all_fresh huniq x y hx hy
  --   have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟xy
  --   have hPnd := HyperEnv.Nodup_perm hP𝒟 hnd
  --   have hPpw := (HyperEnv.Perm_PairwiseDisjoint_iff hP𝒟).mp hpw
  --   simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd hPnd
  --   rw [HyperEnv.merge_assoc] at hpw hPpw
  --   simp only [Finset.union_assoc, Finset.mem_union, not_or, Finset.singleton_union,
  --     Finset.insert_union, Finset.mem_insert, ← ne_eq] at hy hx
  --   have hD := HyperEnv.PairwiseDisjoint_tail_not_in_head hPpw
  --   simp at hD
  --   have hxH := hD.1
  --   have hyH := hD.2 (x := y) (A := ⊥) (Or.inl ⟨rfl, rfl⟩)
  --   change HyperEnv.PairwiseDisjoint (H |ₕ ([[x ∶ 1]] |ₕ [y ∶ ⊥ :: E])) at hPpw
  --   simp [HyperEnv.PairwiseDisjoint_merge] at hPpw
  --   have hDE := HyperEnv.PairwiseDisjoint_implies_disjoint hPpw.2.1
  --   simp only [Env.disjoint, Env.names_distributes, Env.names_nil, Finset.union_empty,
  --     Finset.singleton_union, Finset.disjoint_singleton_left, Finset.mem_insert, not_or] at hDE
  --   simp only [hNamesEq', HyperEnv.names_merge, HyperEnv.names_cons, HyperEnv.names_nil,
  --     Finset.union_empty, Finset.mem_union] at hw
  --   have hw' : w ∈ (H |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: E]).names := by
  --     simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Env.names_distributes,
  --                Finset.mem_union, Finset.mem_singleton] at hw ⊢
  --     rcases hw with hH | hE
  --     · exact Or.inl (Or.inl hH)
  --     · exact Or.inr (Or.inr hE)
  --   rw [← hNamesEq] at hw'
  --   simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff] at hw' ⊢
  --   rcases hw' with  rfl | rfl | hℋ | hΓ
  --   · rcases hw with hwℋ | hwE
  --     · exfalso ; exact hyH hwℋ
  --     · exfalso ; exact hPnd.2.1 hwE
  --   · rcases hw with hwℋ | hwE
  --     · exfalso ; exact hxH hwℋ
  --     · exfalso ; exact hDE.2 hwE
  --   · exact Or.inl hℋ
  --   · exact Or.inr hΓ

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
    have ⟨⟨hx𝒢', hxΓ', hxΔ'⟩, ⟨hy𝒢', hyΓ', hyΔ'⟩⟩ := Typing_res_fresh (huniq' x hx y hy hneq)
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

  case perm hP hP' _ ih =>
    rw [← (HyperEnv.names_eq_of_perm hP), ← (HyperEnv.names_eq_of_perm hP')]
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











lemma TypingStepₘ_inv_one_existential' {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
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
    exact HyperEnv.Perm.extract_one_res_source (A := A)
      (by simp at hP ⊢ ; apply hP) hux hvx

  case perm hP _ _ ih =>
    simp at ih
    have ⟨𝒥, hP'⟩ := ih hl
    use 𝒥
    exact hP.symm.trans hP'

lemma TypingStepₘ_inv_bot_existential' {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
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
    have ⟨⟨hu𝒢, _, huΔ⟩, ⟨hv𝒢, hvΓ, _⟩⟩ := Typing_res_fresh (𝒟 u hu v hv hneq)
    exact HyperEnv.Perm.extract_bot_res_source (A := A)
      (by simp at hP ⊢ ; apply hP) hux hvx hu𝒢 hv𝒢 hneq huΔ hvΓ

  case perm hP _ _ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP'⟩ := ih hl
    use 𝒥, Γ'
    exact hP.symm.trans hP'


lemma TypingStepₘ_inv_one_bot_existential' {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
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
    obtain ⟨𝒥', hP𝒥⟩ := TypingStepₘ_inv_one_existential' hSℰ
    obtain ⟨ℋ', Γ', hPℋ⟩ := TypingStepₘ_inv_bot_existential' hSℱ
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
    have ⟨⟨hu𝒢, huΓ, huΔ⟩, ⟨hv𝒢, hvΓ, hvΔ⟩⟩ := Typing_res_fresh (huinq u hu v hv hneq)
    exact HyperEnv.Perm.extract_one_bot_res_source (A := A)
      (by simp at ⊢ hP' ; exact hP') hux hvx huy hvy hu𝒢 hv𝒢 hneq hvΓ huΔ

  case perm hP _ _ ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP'⟩ := ih hl
    use 𝒢ᵣ, Γᵣ
    exact HyperEnv.Perm.trans hP.symm hP'

lemma TypingStepₘ_inv_one_bot_source' {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  A = 1 ∧ B = ⊥ ∧ Γ = ∅ := by
  obtain ⟨𝒢ᵣ, Γᵣ, hP⟩ := TypingStepₘ_inv_one_bot_existential' hStep
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















lemma TypingStepₘ_inv_one_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧) 𝒟') :
  ∃ 𝒢ᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]]) ∧ (𝒢' ~ 𝒢ᵣ) := by
  generalize hl : (x⟦⟧ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl

  case one =>
    subst hl
    use ∅
    rw [HyperEnv.merge_unitL]
    exact ⟨by rfl, by rfl⟩

  case par₁ ih =>
    expose_names
    simp [HasBracket.brack] at ih
    have ⟨𝒢'', hP1, hP2⟩ := ih hl
    use ℋ |ₕ 𝒢''
    constructor
    · apply HyperEnv.Perm_exchange_lhs HyperEnv.Perm.merge_comm
      rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · apply HyperEnv.Perm.trans HyperEnv.Perm_merge_comm
      exact HyperEnv.Perm_merge_cancel_left_inv hP2

  case par₂ ih =>
    expose_names
    simp [HasBracket.brack] at ih
    have ⟨ℋ''', hP1, hP2⟩ := ih hl
    use 𝒢_1 |ₕ ℋ'''
    constructor
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · exact HyperEnv.Perm_merge_cancel_left_inv hP2

  case res A _ _ _ 𝒟 _ u v hu hv huv hFu hFv _ ih =>
    simp only [HasBracket.brack] at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    subst hl
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, huPf⟩ := hFu
    obtain ⟨hvx, hvPf⟩ := hFv
    have 𝒟' := 𝒟 u hu v hv huv
    have ⟨⟨hu𝒢, huΓ, huΔ⟩, ⟨hv𝒢, hvΓ, hvΔ⟩⟩ := Typing_res_fresh 𝒟'
    exact HyperEnv.Perm.extract_one_res hP1 hP2 hux.symm hvx.symm hu𝒢 hv𝒢 huv huΔ hvΓ

  case perm hP hP' _ ih =>
    simp at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    use 𝒥
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

lemma TypingStepₘ_inv_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ ⊥ :: Γᵣ]) ∧ (𝒢' ~ 𝒢ᵣ |ₕ [Γᵣ]) := by
  generalize hl : (x⸨⸩ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl

  case bot Γ _ _ _ _ _ =>
    subst hl
    use ∅, Γ
    simp only [HyperEnv.merge_unitL]
    exact ⟨by rfl, by rfl⟩

  case par₁ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    expose_names
    use 𝒥 |ₕ ℋ, Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right
      exact HyperEnv.Perm_merge_cancel_right_inv (hP1.trans HyperEnv.Perm_merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP2.trans HyperEnv.Perm_merge_comm

  case par₂ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    expose_names
    use 𝒥 |ₕ 𝒢_1, Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv (hP1.trans HyperEnv.Perm_merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP2.trans HyperEnv.Perm_merge_comm

  case res A _ _ _ 𝒟 𝒟' u v hu hv hneq hFu hFv _ ih =>
    simp only [HasParen.paren] at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    subst hl
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, _⟩ := hFu
    obtain ⟨hvx, _⟩ := hFv
    have ⟨⟨hu𝒢, _, huΔ⟩, ⟨hv𝒢, hvΓ, _⟩⟩ := Typing_res_fresh (𝒟 u hu v hv hneq)
    have ⟨⟨hu𝒢', _, _⟩, ⟨hv𝒢', _, _⟩⟩ := Typing_res_fresh (𝒟' u hu v hv hneq)
    exact HyperEnv.Perm.extract_bot_res
      hP1 hP2 hux.symm hvx.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq huΔ hvΓ

  case perm hP hP' _ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    use 𝒥, Γ'
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

lemma TypingStepₘ_inv_one_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ]) ∧
           (𝒢' ~ 𝒢ᵣ |ₕ [Γᵣ]) := by
  generalize hl : (x⟦()⟧ |ₗ y⸨()⸩) = l at hStep
  induction hStep <;> try simp at hl

  case par₁ ih =>
    expose_names
    obtain ⟨𝒢', Γ', hP1, hP2⟩ := ih hl
    use (𝒢' |ₕ ℋ), Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right at hP1
      apply HyperEnv.Perm_rotate_rhs_left
      rw [← HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_right_inv hP1
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP2.trans HyperEnv.Perm.merge_comm

  case par₂ ih =>
    expose_names
    obtain ⟨ℋ', Γ', hP1, hP2⟩ := ih hl
    use (𝒢_1 |ₕ ℋ'), Γ'
    constructor
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      rw [HyperEnv.merge_assoc] at hP1
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP2

  case syn 𝒥 𝒥' ℋ ℋ' Q Q' R R' l' l'' n' hD1 hD2 ℰ ℰ' ℱ ℱ' hSℰ hSℱ disj lwf ih1 ih2 =>
    rcases hl with ⟨rfl, rfl⟩
    obtain ⟨𝒥', hP𝒥1, hP𝒥2⟩ := TypingStepₘ_inv_one_existential hSℰ
    obtain ⟨ℋ', Γ', hPℋ1, hPℋ2⟩ := TypingStepₘ_inv_bot_existential hSℱ
    use 𝒥' |ₕ ℋ', Γ'
    constructor
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.trans (HyperEnv.Perm.merge hP𝒥1 hPℋ1)
      repeat rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      conv_rhs => rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm_merge_cancel_left_inv
      rw [List.append_eq, List.nil_append]
      apply HyperEnv.Perm_merge_singleton
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm.merge hP𝒥2 hPℋ2

  case res A _ l _ 𝒟 𝒟' u v hu hv hneq hFu hFv hStep ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    subst l
    simp [← ne_eq] at hFu hFv
    obtain ⟨hux, huy, huPf⟩ := hFu
    obtain ⟨hvx, hvy, hvPf⟩ := hFv
    have ⟨⟨hu𝒢, _, huΔ⟩, ⟨hv𝒢, hvΓ, _⟩⟩ := Typing_res_fresh (𝒟 u hu v hv hneq)
    have ⟨⟨hu𝒢', _, _⟩, ⟨hv𝒢', _, _⟩⟩ := Typing_res_fresh (𝒟' u hu v hv hneq)
    exact HyperEnv.Perm.extract_one_bot_res
      hP1 hP2 hux.symm hvx.symm huy.symm hvy.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq hvΓ huΔ

  case perm hP hP' _ ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    use 𝒢ᵣ, Γᵣ
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

lemma TypingStepₘ_inv_one_bot_source {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  A = 1 ∧ B = ⊥ ∧ Γ = ∅ ∧ 𝒢' ~ 𝒢 |ₕ [∅‚ Δ] := by
  obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := TypingStepₘ_inv_one_bot_existential hStep
  have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
  have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟

  have hxLHS : [x ∶ 1] ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] := by
    have hxRHS : [x ∶ 1] ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP1 hxRHS
    simp [HasPerm.perm] at hPΞ
    subst hPΞ
    exact hΞ

  simp [HyperEnv.PairwiseDisjoint_merge] at hpw
  have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1

  have hyLHS : ∃ Γ', Γ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Γ' ~ y ∶ ⊥ :: Γᵣ := by
    have hyRHS : (y ∶ ⊥ :: Γᵣ) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP1 hyRHS
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
      · refine ⟨(y ∶ ⊥ :: Δ), by simp, hPΞ⟩
      · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ h)

  simp at hxLHS hyLHS
  rcases hxLHS with h1 | h2 | h3
  · exfalso
    apply HyperEnv.not_mem_names_iff.mp hx𝒢 [x ∶ 1] 1 h1
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  · rcases h2 with ⟨rfl, rfl⟩
    · have ⟨Ξ, hΞ, hPΞ⟩ := hyLHS
      have hyΞ := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      rcases hΞ with h4 | h5 | h6
      · exfalso
        exact HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ ⊥ h4 hyΞ
      · subst h5
        simp [HasPerm.perm] at hPΞ
      · subst h6
        simp at hyΞ
        rcases hyΞ with rfl | h2
        · have hPΞ' := hPΞ
          simp [HasPerm.perm] at ⊢ hPΞ'
          apply HyperEnv.Perm_singleton_singleton.mpr at hPΞ'
          apply HyperEnv.Perm_singleton_singleton.mpr at hPΞ
          have hP1': 𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Δ] :=
            hP1.trans (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPΞ.symm)
          apply HyperEnv.Perm_merge_cancel_right at hP1'
          apply HyperEnv.Perm_merge_cancel_right at hP1'
          exact hP2.trans (HyperEnv.Perm.merge hP1'.symm hPΞ'.symm)
        · exfalso ; apply hyΔ
          exact Env.mem_pair_fst_in_names _ h2
  · obtain ⟨⟨rfl, _⟩, _⟩ := h3
    simp at hDΓΔ

lemma TypingStepₘ_inv_one_bot {n n' : Nat} {P P' : Proc} {𝒢ᵣ 𝒢' : HyperEnv}
  {x y : FPName} {A : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢ᵣ |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  𝒢' ~ 𝒢ᵣ |ₕ [Γ‚ Δ] := by
  have ⟨hA, hB, rfl, hP⟩ := TypingStepₘ_inv_one_bot_source 𝒟 hStep
  exact hP

























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
    exact TypingStepₘ.perm (𝒟' := 𝒟') hP.symm (by rfl) (TypingStepₘ.bot (hF := hxΓ))


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
      apply TypingStepₘ.perm hP.symm (by rfl)
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
      apply TypingStepₘ.perm hP.symm (by rfl)
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
    apply TypingStepₘ.perm hP.symm (by rfl)
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
    apply TypingStepₘ.perm hP.symm (by rfl)
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
    · apply TypingStepₘ.perm hP.symm (by rfl)
      · apply TypingStepₘ.syn
        · exact hD
        · exact hD'
        · exact hStepRR'
        · exact hStepQQ'
        · exact disj
        · exact lwf
    · exact hD'

  case one_bot Q Q' x y hxQf hyQf hxy hPS ih =>
    have ⟨A, Γ, Δ, ℋ, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    have hNames := Typing.f_eq_names 𝒟
    simp [HyperEnv.names_eq_of_perm hP] at hNames
    let hxQf' := hxQf
    let hyQf' := hyQf
    simp [hNames, -Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff] at hxQf' hyQf'
    obtain ⟨hxℋ, hxΓ, hxΔ⟩ := hxQf'
    obtain ⟨hyℋ, hyΓ, hyΔ⟩ := hyQf'
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      exists_two_fresh (L ∪ Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names ∪ {x, y})
    simp [← ne_eq, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at hz hw
    obtain ⟨hzx, hzy, hzL, hzQf, hzℋ, hzΓ, hzΔ⟩ := hz
    obtain ⟨hwx, hwy, hwL, hwQf, hwℋ, hwΓ, hwΔ⟩ := hw
    have hx_bound_t : x ∉ ({y} ∪ Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq]
      exact ⟨⟨⟨⟨hxy, hxQf⟩, hxℋ⟩, hxΓ⟩, hxΔ⟩
    have hy_bound_t : y ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hyQf, hyℋ⟩, hyΓ⟩, hyΔ⟩
    have hx_bound : x ∉ ({y} ∪ Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq]
      exact ⟨⟨⟨hxy, hxQf⟩, hxℋ⟩, hxΔ⟩
    have hy_bound : y ∉ (Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨hyQf, hyℋ⟩, hyΔ⟩
    have 𝒟xy := (Typing_res_all_fresh 𝒟' x y hx_bound_t hy_bound_t)
    have ⟨_, _, hPS_t⟩ := ih 𝒟xy
    have ⟨hA, hB, hΓ, _⟩ := TypingStepₘ_inv_one_bot_source 𝒟xy hPS_t
    subst hA hΓ
    rw! [hB] at *
    have := (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    obtain ⟨𝒢', 𝒟'', hPS'⟩ := ih (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    have ⟨_, _, _, hP𝒢'⟩ := TypingStepₘ_inv_one_bot_source this hPS'
    refine ⟨𝒢', 𝒟'', ?_⟩
    apply TypingStepₘ.perm hP.symm hP𝒢'.symm
    · apply TypingStepₘ.one_bot (𝒢' := 𝒢') (huniq := 𝒟') (hx := hx_bound) (hy := hy_bound)
      · exact TypingStepₘ.perm (by rfl) hP𝒢' hPS'

  case tensor_parr L _ ih =>
    sorry -- FIXME:

  case res =>
    have ⟨A, Γ, Δ, 𝒢, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    sorry -- FIXME:














-- theorem subject_reductionₘ {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
--   (𝒟 : Typing n P 𝒢) (hPS : ProcStepₘ P l P') :
--   ∃ 𝒢', EnvStepₘ 𝒢 l 𝒢' ∧ (Typing n P' 𝒢') := by
--   obtain ⟨𝒢', 𝒟', hTS⟩ := typability_subject_reductionₘ 𝒟 hPS
--   have hES := session_fidelity_envₘ hTS
--   exact ⟨𝒢', hES, 𝒟'⟩






















/-
  Together session_fidelity_procₘ and typability_subject_reductionₘ establishes the Strong
  Bisimulation required by Theorem 4.7.
-/

-- TODO: Prove Session fidelity, erasure, type preservation, Session fidelity for πLL
/- TODO:
  - Remove _source variants of TypingStep inversion lemmas
    and their respective extract perm and existential variants (not existential')
  - But also rename existential' to something else
-/
