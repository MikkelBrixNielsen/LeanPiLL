import PiLL.Substitution
import PiLL.Semantics.Labels

-- Same reason as in Environment.lean
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

-- FIXME: Move to Judgment
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

macro "clean_subst' " T:ident h1:ident h2:ident h3:ident h4:ident h5:ident
  h6:ident h7:ident h8:ident : tactic =>
  `(tactic|
      simp only [HyperEnv.substNames_of_not_mem $h1, Env.substNames_of_not_mem $h2,
        Env.substNames_of_not_mem $h3, Env.substNames_of_not_mem $h4,
        Proc.open_two_substNames_gen, Proc.substNames_of_not_mem $h5,
        FPName.subst_self, FPName.subst_self_of_ne $h6,
        FPName.subst_self_of_ne $h7, FPName.subst_self_of_ne $h8] at $T:ident
  )

macro "clean_substNames "
  T:ident h𝒢:ident hΓ:ident hΔ:ident hfpn:ident hpf:ident : tactic =>
  `(tactic|
      distribute_names $T <;>
      clean_subst $T $h𝒢 $hΓ $hΔ $hpf $hfpn
    )

macro "clean_substNames' " T:ident h1:ident h2:ident h3:ident h4:ident h5:ident
  h6:ident h7:ident h8:ident : tactic =>
  `(tactic|
      distribute_names $T <;>
      clean_subst' $T $h1 $h2 $h3 $h4 $h5 $h6 $h7 $h8
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

lemma Typing_res_all_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv}
  {Γ Δ : Env} {A B : Types} {L : Finset FPName}
  (huniq : ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
    Typing n (P⸨#z, #w⸩) (𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ B :: Δ])) :
  ∀ x y,
  x ∉ (P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names) →
  y ∉ (P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names) → x ≠ y →
  Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ]) := by
  intros x y hFx hFy hxy
  obtain ⟨z, w, hz, hw, hzw⟩ :=
    exists_two_fresh (L ∪ {x, y} ∪ 𝒢.names ∪ Γ.names ∪ Δ.names ∪ P.f)
  simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq] at hFx hFy hz hw
  obtain ⟨hzL, hzx, hzy, hz𝒢, hzΓ, hzΔ, hzPf⟩ := hz
  obtain ⟨hwL, hwx, hwy, hw𝒢, hwΓ, hwΔ, hwPf⟩ := hw
  obtain ⟨hxPf, hx𝒢, hxΓ, hxΔ⟩ := hFx
  obtain ⟨hyPf, hy𝒢, hyΓ, hyΔ⟩ := hFy
  have 𝒟zw := huniq z hzL w hwL hzw
  have 𝒟xw := Typing_substNames (x := z) (y := x) 𝒟zw
    (HyperEnv.substNames_res_left (Γ := Γ) (Δ := Δ) hx𝒢 hxΓ hxΔ hwx.symm)
  clean_substNames 𝒟xw hz𝒢 hzΓ hzΔ hzw.symm hzPf
  have 𝒟xy := Typing_substNames (x := w) (y := y) 𝒟xw
    (HyperEnv.substNames_res_right (Γ := Γ) (Δ := Δ) hy𝒢 hyΓ hyΔ hxy.symm)
  clean_substNames 𝒟xy hw𝒢 hwΓ hwΔ hwx.symm hwPf
  exact 𝒟xy





-- FIXME: Move to Environment
lemma HyperEnv.mem_tensor_parr_post_env
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ], ∀ C, (z, C) ∈ Ξ →
  z = x ∨ z = x' ∨ z = y ∨ z = y' := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl | rfl
  · exfalso
    exact hz𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exact Or.inl rfl
    · exfalso
      exact hzΓ₁ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exact Or.inr (Or.inl rfl)
    · exfalso
      exact hzΓ₂ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exfalso
      exact hzΔ (Env.mem_pair_fst_in_names _ h)

lemma HyperEnv.substNames_tensor_parr_x
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx' : z ≠ x') (hzy' : z ≠ y') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = x := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact h
  · exact False.elim (hzx' h)
  · exact False.elim (hzy h)
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_x'
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzy' : z ≠ y') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = x' := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact h
  · exact False.elim (hzy h)
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_y
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzx' : z ≠ x') (hzy' : z ≠ y') :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = y := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact False.elim (hzx' h)
  · exact h
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_y'
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzx' : z ≠ x') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = y' := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact False.elim (hzx' h)
  · exact False.elim (hzy h)
  · exact h



-- FIXME: Move to Judgemnt
lemma unpack_tensor_parr_fresh {v : FPName} {L : Finset FPName}
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} (hv : v ∉ L)
  (hEnv : 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names ⊆ L) :
  v ∉ 𝒢.names ∧ v ∉ Γ₁.names ∧ v ∉ Γ₂.names ∧ v ∉ Δ.names := by
  have h1 : v ∉ 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names := fun h => hv (hEnv h)
  simp only [Finset.mem_union, not_or, Env.names_merge] at h1
  exact ⟨h1.1.1, h1.1.2.1, h1.1.2.2, h1.2⟩

lemma Typing_tensor_parr_post_f_avoid {m : Nat} {P : Proc} {𝒢 : HyperEnv}
  {Γ₁ Γ₂ Δ : Env} {A B : Types} {x y x' y' a : FPName}
  (𝒟 : m ⊢ P⸨2 | #x, #y⸩⸨#x', #y'⸩ ∷
    𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ])
  (hax : a ≠ x) (hax' : a ≠ x') (hay : a ≠ y) (hay' : a ≠ y')
  (ha𝒢 : a ∉ 𝒢.names) (haΓ₁ : a ∉ Γ₁.names) (haΓ₂ : a ∉ Γ₂.names) (haΔ : a ∉ Δ.names) :
  a ∉ (P⸨2 | #x, #y⸩⸨#x', #y'⸩).f := by
  rw [Typing.f_eq_names 𝒟]
  simp only [List.append_assoc, List.cons_append, List.nil_append, HyperEnv.names_merge,
    HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union, Finset.union_insert,
    HyperEnv.names_nil, Finset.union_empty, Finset.insert_union, Finset.mem_insert,
    Finset.mem_union, not_or, ← ne_eq]
  exact ⟨hay, hay', hax', hax, ha𝒢, haΓ₁, haΓ₂, haΔ⟩

lemma Typing_tensor_parr_post_all_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv}
  {Γ₁ Γ₂ Δ : Env} {A B : Types} {x y x' y' : FPName} (L : Finset FPName)
  (𝒟 : n ⊢ P⸨2 | #x, #y⸩⸨#x', #y'⸩ ∷
    𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ])
  (hx : x ∉ L) (hy : y ∉ L) (hx' : x' ∉ L) (hy' : y' ∉ L)
  (hEnv : 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names ⊆ L)
  (hxPf : x ∉ P.f) (hyPf : y ∉ P.f) (hx'Pf : x' ∉ P.f) (hy'Pf : y' ∉ P.f)
  (hxx' : x ≠ x') (hxy : x ≠ y) (hxy' : x ≠ y')
  (hyx' : y ≠ x') (hyy' : y ≠ y') (hx'y' : x' ≠ y') :
  ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
  ∀ z' ∉ L, ∀ w' ∉ L, z' ≠ w' →
  z ≠ z' → z ≠ w' → w ≠ z' → w ≠ w' →
  n ⊢ P⸨2 | #z, #w⸩⸨#z', #w'⸩ ∷
    𝒢 |ₕ [z ∶ B :: Γ₁] |ₕ [z' ∶ A :: Γ₂] |ₕ [w' ∶ Aᗮ :: w ∶ Bᗮ :: Δ] := by
  intros z hz w hw hzw z' hz' w' hw' hz'w' hzz' hzw' hwz' hww'
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_fresh (L ∪ {x, y, x', y', z, w, z', w'} ∪
    P.f ∪ 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names)
  obtain ⟨a', b', ha', hb', ha'b'⟩ := exists_two_fresh (L ∪ {x, y, x', y', z, w, z', w', a, b} ∪
    P.f ∪ 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names)
  simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq, Env.names_merge]
    at ha hb ha' hb'
  obtain ⟨hx𝒢, hxΓ₁, hxΓ₂, hxΔ⟩ := unpack_tensor_parr_fresh hx hEnv
  obtain ⟨hy𝒢, hyΓ₁, hyΓ₂, hyΔ⟩ := unpack_tensor_parr_fresh hy hEnv
  obtain ⟨hx'𝒢, hx'Γ₁, hx'Γ₂, hx'Δ⟩ := unpack_tensor_parr_fresh hx' hEnv
  obtain ⟨hy'𝒢, hy'Γ₁, hy'Γ₂, hy'Δ⟩ := unpack_tensor_parr_fresh hy' hEnv
  obtain ⟨hz𝒢, hzΓ₁, hzΓ₂, hzΔ⟩ := unpack_tensor_parr_fresh hz hEnv
  obtain ⟨hw𝒢, hwΓ₁, hwΓ₂, hwΔ⟩ := unpack_tensor_parr_fresh hw hEnv
  obtain ⟨hz'𝒢, hz'Γ₁, hz'Γ₂, hz'Δ⟩ := unpack_tensor_parr_fresh hz' hEnv
  obtain ⟨hw'𝒢, hw'Γ₁, hw'Γ₂, hw'Δ⟩ := unpack_tensor_parr_fresh hw' hEnv
  obtain ⟨haL, hax, hay, hax', hay', haz, haw, haz', haw', haPf, ha𝒢, haΓ₁, haΓ₂, haΔ⟩ := ha
  obtain ⟨hbL, hbx, hby, hbx', hby', hbz, hbw, hbz', hbw', hbPf, hb𝒢, hbΓ₁, hbΓ₂, hbΔ⟩ := hb
  obtain ⟨ha'L, ha'x, ha'y, ha'x', ha'y', ha'z, ha'w, ha'z', ha'w', ha'a, ha'b,
    ha'Pf, ha'𝒢, ha'Γ₁, ha'Γ₂, ha'Δ⟩ := ha'
  obtain ⟨hb'L, hb'x, hb'y, hb'x', hb'y', hb'z, hb'w, hb'z', hb'w', hb'a, hb'b,
    hb'Pf, hb'𝒢, hb'Γ₁, hb'Γ₂, hb'Δ⟩ := hb'
  have 𝒟 := Typing_substNames (x := x) (y := a) 𝒟
    (HyperEnv.substNames_tensor_parr_x ha𝒢 haΓ₁ haΓ₂ haΔ hax' hay' hay)
  clean_substNames' 𝒟 hx𝒢 hxΓ₁ hxΓ₂ hxΔ hxPf hxy.symm hxx'.symm hxy'.symm
  have 𝒟 := Typing_substNames (x := y) (y := b) 𝒟
    (HyperEnv.substNames_tensor_parr_y hb𝒢 hbΓ₁ hbΓ₂ hbΔ hab.symm hbx' hby')
  clean_substNames' 𝒟 hy𝒢 hyΓ₁ hyΓ₂ hyΔ hyPf hay hyx'.symm hyy'.symm
  have 𝒟 := Typing_substNames (x := x') (y := a') 𝒟
    (HyperEnv.substNames_tensor_parr_x' ha'𝒢 ha'Γ₁ ha'Γ₂ ha'Δ ha'a ha'y' ha'b)
  clean_substNames' 𝒟 hx'𝒢 hx'Γ₁ hx'Γ₂ hx'Δ hx'Pf hax' hbx' hx'y'.symm
  have 𝒟 := Typing_substNames (x := y') (y := b') 𝒟
    (HyperEnv.substNames_tensor_parr_y' hb'𝒢 hb'Γ₁ hb'Γ₂ hb'Δ hb'a ha'b'.symm hb'b)
  clean_substNames' 𝒟 hy'𝒢 hy'Γ₁ hy'Γ₂ hy'Δ hy'Pf hay' hby' ha'y'
  have 𝒟 := Typing_substNames (x := a) (y := z) 𝒟
    (HyperEnv.substNames_tensor_parr_x hz𝒢 hzΓ₁ hzΓ₂ hzΔ ha'z.symm hb'z.symm hbz.symm)
  clean_substNames' 𝒟 ha𝒢 haΓ₁ haΓ₂ haΔ haPf hab.symm ha'a hb'a
  have 𝒟 := Typing_substNames (x := b) (y := w) 𝒟
    (HyperEnv.substNames_tensor_parr_y hw𝒢 hwΓ₁ hwΓ₂ hwΔ hzw.symm ha'w.symm hb'w.symm)
  clean_substNames' 𝒟 hb𝒢 hbΓ₁ hbΓ₂ hbΔ hbPf hbz.symm ha'b hb'b
  have 𝒟 := Typing_substNames (x := a') (y := z') 𝒟
    (HyperEnv.substNames_tensor_parr_x' hz'𝒢 hz'Γ₁ hz'Γ₂ hz'Δ hzz'.symm hb'z'.symm hwz'.symm)
  clean_substNames' 𝒟 ha'𝒢 ha'Γ₁ ha'Γ₂ ha'Δ ha'Pf ha'z.symm ha'w.symm ha'b'.symm
  have 𝒟 := Typing_substNames (x := b') (y := w') 𝒟
    (HyperEnv.substNames_tensor_parr_y' hw'𝒢 hw'Γ₁ hw'Γ₂ hw'Δ hzw'.symm hz'w'.symm hww'.symm)
  clean_substNames' 𝒟 hb'𝒢 hb'Γ₁ hb'Γ₂ hb'Δ hb'Pf hb'z.symm hb'w.symm hb'z'.symm
  exact 𝒟

lemma unpack_res_fresh {v : FPName} {L : Finset FPName}
  {𝒢 : HyperEnv} {Γ Δ : Env} (hv : v ∉ L)
  (hEnv : 𝒢.names ∪ Γ.names ∪ Δ.names ⊆ L) :
  v ∉ 𝒢.names ∧ v ∉ Γ.names ∧ v ∉ Δ.names := by
  have h1 : v ∉ 𝒢.names ∪ Γ.names ∪ Δ.names := fun h => hv (hEnv h)
  simp only [Finset.mem_union, not_or, or_assoc] at h1
  exact h1

lemma Typing_res_post_all_fresh {n : Nat} {P : Proc} {𝒢 : HyperEnv}
  {Γ Δ : Env} {A : Types} {x y : FPName} (L : Finset FPName)
  (𝒟 : n ⊢ P⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])
  (hx : x ∉ L) (hy : y ∉ L) (hxPf : x ∉ P.f) (hyPf : y ∉ P.f)
  (hEnv : 𝒢.names ∪ Γ.names ∪ Δ.names ⊆ L) (hxy : x ≠ y) :
  ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
    n ⊢ P⸨#z, #w⸩ ∷ 𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ Aᗮ :: Δ] := by
  intros z hz w hw hzw
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_fresh (L ∪ {x, y, z, w} ∪
    P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names)
  simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc,
    Finset.mem_insert, Finset.mem_union, not_or, ← ne_eq]
    at ha hb
  obtain ⟨haL, hax, hay, haz, haw, haPf, ha𝒢, haΓ, haΔ⟩ := ha
  obtain ⟨hbL, hbx, hby, hbz, hbw, hbPf, hb𝒢, hbΓ, hbΔ⟩ := hb
  obtain ⟨hx𝒢, hxΓ, hxΔ⟩ := unpack_res_fresh hx hEnv
  obtain ⟨hy𝒢, hyΓ, hyΔ⟩ := unpack_res_fresh hy hEnv
  obtain ⟨hz𝒢, hzΓ, hzΔ⟩ := unpack_res_fresh hz hEnv
  obtain ⟨hw𝒢, hwΓ, hwΔ⟩ := unpack_res_fresh hw hEnv
  have 𝒟 := Typing_substNames (x := x) (y := a) 𝒟
    (HyperEnv.substNames_res_left ha𝒢 haΓ haΔ hay)
  clean_substNames 𝒟 hx𝒢 hxΓ hxΔ hxy.symm hxPf
  have 𝒟 := Typing_substNames (x := y) (y := b) 𝒟
    (HyperEnv.substNames_res_right hb𝒢 hbΓ hbΔ hab.symm)
  clean_substNames 𝒟 hy𝒢 hyΓ hyΔ hay hyPf

  have 𝒟 := Typing_substNames (x := a) (y := z) 𝒟
    (HyperEnv.substNames_res_left hz𝒢 hzΓ hzΔ hbz.symm)
  clean_substNames 𝒟 ha𝒢 haΓ haΔ hab.symm haPf
  have 𝒟 := Typing_substNames (x := b) (y := w) 𝒟
    (HyperEnv.substNames_res_right hw𝒢 hwΓ hwΔ hzw.symm)
  clean_substNames 𝒟 hb𝒢 hbΓ hbΔ hbz.symm hbPf
  exact 𝒟

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

abbrev Typing_double_cut_tensor_parr
  {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P' : Proc} {A B : Types} {n : Nat} {L : Finset FPName}
  (huniq' : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ∀ x' ∉ L, ∀ y' ∉ L, x' ≠ y' →
    x ≠ x' → x ≠ y' → y ≠ x' → y ≠ y' →
     Typing n (P'⸨2 | #x, #y⸩⸨#x', #y'⸩)
      (𝒢 |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ])) :
  Typing n (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P')) (𝒢 |ₕ [Γ‚ (Δ‚ Ξ)]) :=
  Typing.exchange_hyper
    (Typing.cut L (A := B) (fun z hz w hw hzw =>
      Typing.exchange_hyper
        (Typing.cut (L ∪ {z, w}) (A := A) (fun z' hz' w' hw' hzw' => by
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, not_or, ← ne_eq] at hz' hw'
          exact huniq' z hz w hw hzw z' hz'.1 w' hw'.1 hzw'
            hz'.2.1.symm hw'.2.1.symm hz'.2.2.symm hw'.2.2.symm))
        (HyperEnv.Perm.merge (HyperEnv.Perm_refl)
          (HyperEnv.Perm_singleton_singleton.mpr List.perm_middle)
        )))
    (HyperEnv.Perm.merge
      (HyperEnv.Perm.refl _)
      (HyperEnv.Perm_singleton_singleton.mpr (List.perm_append_comm_assoc _ _ _))
    )

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
      {𝒟' : Typing n P' (𝒢 |ₕ [∅‚ Γ])}
      (hStep : TypingStepₘ (Typing_one_bot_all_fresh huniq x y hx hy) (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'

| tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {A B : Types} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
        Typing n
          (P⸨#x, #y⸩)
          (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])}
      {huniq' : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ∀ x' ∉ L, ∀ y' ∉ L, x' ≠ y' →
        x ≠ x' → x ≠ y' → y ≠ x' → y ≠ y' →
        Typing n
          (P'⸨2 | #x, #y⸩⸨#x', #y'⸩)
          (𝒢 |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ])}
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      {x' y' : FPName} (hx' : x' ∉ L) (hy' : y' ∉ L) (hneq' : x' ≠ y')
      (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x') (hyy' : y ≠ y')
      (hxP : x ∉ P.f) (hyP : y ∉ P.f) (hx'P : x' ∉ P.f) (hy'P : y' ∉ P.f)
      (hxP' : x ∉ P'.f) (hyP' : y ∉ P'.f) (hx'P' : x' ∉ P'.f) (hy'P' : y' ∉ P'.f)
      (hStep : TypingStepₘ (huniq x hx y hy hneq) (x⟦x'⟧ |ₗ y⸨y'⸩)
        (huniq' x hx y hy hneq x' hx' y' hy' hneq' hxx' hxy' hyx' hyy')) :
      TypingStepₘ
        (Typing.cut L huniq)
        (τ)
        (Typing_double_cut_tensor_parr huniq')

| res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {A : Types} {n : Nat} {l : Lbl}
      {L L' : Finset FPName}
      {huniq : ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
        Typing n (P⸨#z, #w⸩) (𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ Aᗮ :: Δ])}
      {huniq' : ∀ z ∉ L', ∀ w ∉ L', z ≠ w →
        Typing n (P'⸨#z, #w⸩) (𝒢' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'])}
      {x y : FPName} (hneq : x ≠ y)
      (hx_pre : x ∉ P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names)
      (hy_pre : y ∉ P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names)
      (hx_post : x ∉ P'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names)
      (hy_post : y ∉ P'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names)
      (hlx : x ∉ l.f ∪ l.i) (hly : y ∉ l.f ∪ l.i)
      (hStep : TypingStepₘ
        (Typing_res_all_fresh huniq x y hx_pre hy_pre hneq) l
        (Typing_res_all_fresh huniq' x y hx_post hy_post hneq)) :
      ---------------------------------------------------------
      TypingStepₘ (Typing.cut L huniq) l (Typing.cut L' huniq')

  ------- Additional Structural / Exchange Rules -------

  | perm_env {𝒢 ℋ : HyperEnv} {Γ Γ' : Env} {P P' : Proc} {n n' : Nat} {l : Lbl}
    {𝒟 : n ⊢ P ∷ (Γ :: 𝒢)} {𝒟' : n' ⊢ P' ∷ ℋ} (hP1 : Γ ~ Γ')
    (hTS : TypingStepₘ 𝒟 l 𝒟') :
    TypingStepₘ (Typing.exchange_env 𝒟 hP1) l 𝒟'

  | perm_hyper {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' : Proc} {n n' : Nat} {l : Lbl}
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
        (𝒢 |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ]) →
      ------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ‚ Ξ]) (τ) (𝒢 |ₕ [Γ‚ Δ‚ Ξ])

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A : Types} {l : Lbl}
      (hFx : x ∉ l.i ∪ l.f) (hFy : y ∉ l.i ∪ l.f) :
      EnvStepₘ (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) (l) (𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStepₘ (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])

  ------- Additional Structural / Exchange Rules -------

  | perm_env {𝒢 ℋ : HyperEnv} {Γ Γ' : Env} {l : Lbl} (hP1 : Γ ~ Γ') :
      (hES : EnvStepₘ (Γ :: 𝒢) l ℋ) →
      ---------------------------------
      EnvStepₘ (Γ' :: 𝒢) l ℋ

  | perm_hyper {𝒢 𝒢' ℋ ℋ' : HyperEnv} {l : Lbl} (hP1 : 𝒢 ~ 𝒢') (hP2 : ℋ ~ ℋ') :
      (hES : EnvStepₘ 𝒢 l ℋ) →
      -------------------------
      EnvStepₘ 𝒢' l ℋ'


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
    simp only [env] at ⊢ ih
    rw [← Env.merge_assoc]
    exact EnvStepₘ.tensor_parr ih

  case res hlx hly _ ih =>
    apply EnvStepₘ.res ?_ ?_ ih
    all_goals
      simp only [Finset.mem_union, not_or] at hlx hly ⊢
    · exact ⟨hlx.2, hlx.1⟩
    · exact ⟨hly.2, hly.1⟩

  case perm_hyper hP hP' hTS ih => exact EnvStepₘ.perm_hyper hP hP' ih

  case perm_env hP hTS ih => exact EnvStepₘ.perm_env hP ih

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
      (hxP : x ∉ P.f) (hyP : y ∉ P.f) (hx'P : x' ∉ P.f) (hy'P : y' ∉ P.f)
      (hxP' : x ∉ P'.f) (hyP' : y ∉ P'.f) (hx'P' : x' ∉ P'.f) (hy'P' : y' ∉ P'.f)
      (hxx' : x ≠ x') (hxy : x ≠ y) (hxy' : x ≠ y')
      (hyx' : y ≠ x') (hyy' : y ≠ y') (hx'y' : x' ≠ y')
      (hStep : ProcStepₘ P⸨#x, #y⸩ (x⟦x'⟧ |ₗ y⸨y'⸩) P'⸨2 | #x, #y⸩⸨#x', #y'⸩) :
      -----------------------------------------------------------------------
      ProcStepₘ (𝑣⸨$N,$N⸩ P) (τ) (𝑣⸨$N,$N⸩ (𝑣⸨$N,$N⸩ P'))

| res
      {P P' : Proc} {l : Lbl} {x y : FPName}  (hneq : x ≠ y)
      (hx : x ∉ P.f ∪ P'.f) (hFy : y ∉ P.f ∪ P'.f)
      (hlx : x ∉ l.f ∪ l.i) (hly : y ∉ l.f ∪ l.i)
      (hStep : ProcStepₘ P⸨#x, #y⸩ l P'⸨#x, #y⸩) :
      -------------------------------------------
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

  case tensor_parr ih =>
    expose_names
    simp only [proc] at ⊢ ih
    apply ProcStepₘ.tensor_parr hxP hyP hx'P hy'P hxP' hyP' hx'P' hy'P'
      hxx' hneq hxy' hyx' hyy' hneq' ih

  case res ih =>
    expose_names
    simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
      at hx_pre hx_post hy_pre hy_post
    have h1 : x ∉ P_1.f ∪ P'_1.f := by simp [hx_pre, hx_post]
    have h2 : y ∉ P_1.f ∪ P'_1.f := by simp [hy_pre, hy_post]
    exact ProcStepₘ.res hneq h1 h2 hlx hly ih

  case perm_hyper ih | perm_env ih => exact ih

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

  case res 𝒢' _ Γ' _ Δ' _ _ A _ _ _ _ _ huniq' x y hneq hx hy hx' hy' hlx hly hStep ih =>
    intro a ha
    simp only [HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge, HyperEnv.names_nil,
      Finset.union_empty, Finset.mem_union, List.append_assoc, List.cons_append,
      List.nil_append, Env.names_distributes, Finset.singleton_union, Finset.union_insert,
      Finset.insert_union, Finset.union_assoc] at ha ih ⊢
    have haLHS : a ∈ insert y (insert x (𝒢'.names ∪ (Γ'.names ∪ Δ'.names))) := by
      simp only [Finset.mem_insert, Finset.mem_union, ha, or_true]
    have haRHS := ih haLHS
    simp only [Finset.mem_insert, Finset.mem_union] at haRHS
    simp only [Finset.notMem_union, and_assoc] at hx hy hx' hy'
    obtain ⟨hxPf', hx𝒢', hxΓ', hxΔ'⟩ := hx'
    obtain ⟨hyPf', hy𝒢', hyΓ', hyΔ'⟩ := hy'
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

  case perm_hyper hP hP' _ ih =>
    rw [← (HyperEnv.names_eq_of_perm hP), ← (HyperEnv.names_eq_of_perm hP')]
    exact ih

  case perm_env hP _ ih =>
    simp only [HyperEnv.names_cons, Finset.union_assoc] at ⊢ ih
    rw [← (Env.names_eq_of_perm hP)]
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
    · apply HyperEnv.Perm.trans HyperEnv.Perm.merge_comm
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

  case res A _ _ _ 𝒟 _ u v huv hu hv hu' hv' hlu hlv _ ih =>
    simp only [HasBracket.brack] at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    subst hl
    simp only [Finset.union_assoc, Finset.mem_union, not_or, Lbl.f, fNamesAct, Lbl.i,
      iNamesAct, Finset.union_empty, Finset.mem_singleton, ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨_, hu𝒢, huΓ, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, hvΔ⟩ := hv
    exact HyperEnv.Perm.extract_one_res hP1 hP2 hlu.symm hlv.symm hu𝒢 hv𝒢 huv huΔ hvΓ

  case perm_hyper hP hP' _ ih =>
    simp at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    use 𝒥
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp at ih
    have ⟨𝒥, hP1, hP2⟩ := ih hl
    use 𝒥
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2

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
      exact HyperEnv.Perm_merge_cancel_right_inv (hP1.trans HyperEnv.Perm.merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP2.trans HyperEnv.Perm.merge_comm

  case par₂ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    expose_names
    use 𝒥 |ₕ 𝒢_1, Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv (hP1.trans HyperEnv.Perm.merge_comm)
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP2.trans HyperEnv.Perm.merge_comm

  case res A _ _ _ 𝒟 𝒟' u v hneq hu hv hu' hv' hlu hlv _ ih =>
    simp only [HasParen.paren] at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    subst hl
    simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff,
      ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨_, hu𝒢, _, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, _⟩ := hv
    obtain ⟨_, hu𝒢', _, _⟩ := hu'
    obtain ⟨_, hv𝒢', _, _⟩ := hv'
    exact HyperEnv.Perm.extract_bot_res
      hP1 hP2 hlu.symm hlv.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq huΔ hvΓ

  case perm_hyper hP hP' _ ih =>
    simp at ih
    have ⟨𝒥, Γ', hP1, hP2⟩ := ih hl
    use 𝒥, Γ'
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp at ih
    have ⟨𝒥, Ξ, hP1, hP2⟩ := ih hl
    use 𝒥, Ξ
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2

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

  case res A _ l _ _ 𝒟 𝒟' u v hneq hu hv hu' hv' hlu hlv hStep ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    subst l
    simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff,
      ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨hux, huy⟩ := hlu
    obtain ⟨hvx, hvy⟩ := hlv
    obtain ⟨_, hu𝒢, _, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, _⟩ := hv
    obtain ⟨_, hu𝒢', _, _⟩ := hu'
    obtain ⟨_, hv𝒢', _, _⟩ := hv'
    exact HyperEnv.Perm.extract_one_bot_res
      hP1 hP2 hux.symm hvx.symm huy.symm hvy.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq hvΓ huΔ

  case perm_hyper hP hP' _ ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    use 𝒢ᵣ, Γᵣ
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2

  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp at ih ⊢
    have ⟨𝒥, Ξ, hP1, hP2⟩ := ih hl
    use 𝒥, Ξ
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2

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

lemma TypingStepₘ_inv_tensor_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧) 𝒟') :
  ∃ 𝒢ᵣ Γ₁ Γ₂ C D,
    x ≠ x' ∧
    (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γ₁‚ Γ₂]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁]) := by
  generalize hl : (x⟦x'⟧ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl
  case tensor =>
    expose_names
    obtain ⟨h1, h2⟩ := hl
    subst h1 h2
    use ∅, Γ, Δ, A, B
    simp [← ne_eq] at hy
    refine ⟨hy.1.symm, by simp, ?_⟩
    rw [HyperEnv.merge_unitL]
    exact HyperEnv.Perm.trans HyperEnv.Perm.merge_comm (HyperEnv.Perm.refl _)
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥 |ₕ ℋ, Γ, Δ, A, B, hxx',  ?_, ?_⟩
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_exchange_rhs (HyperEnv.Perm.merge_comm) hP
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_rotate_rhs_right hP'
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒢_1 |ₕ 𝒥, Γ, Δ, A, B, hxx', ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      rw [← HyperEnv.merge_assoc]
      exact hP'
  case res 𝒥 𝒥' Γ Γ' Δ Δ' Q Q' A m l' L L' huniq huniq' z w hzw
    hz_pre hw_pre hz_post hw_post hlz hlw _ ih =>
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒦, Γ₁, Γ₂, C, D, hxx', hP, hP'⟩ := ih
    simp only [Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.mem_union, not_or,
      Finset.notMem_singleton] at hlz hlw
    obtain ⟨hzx, hzx'⟩ := hlz
    obtain ⟨hyx, hyx'⟩ := hlw
    simp only [Finset.mem_union, not_or, and_assoc] at hz_pre hw_pre hz_post hw_post
    have hP'' : 𝒥' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'] ~
      𝒦 |ₕ [x' ∶ C :: Γ₁] |ₕ [x ∶ D :: Γ₂] := by
      have :  𝒦 |ₕ [x' ∶ C :: Γ₁] |ₕ [x ∶ D :: Γ₂] ~ 𝒦 |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁] := by
        simp only [HyperEnv.merge_assoc]
        exact HyperEnv.Perm.merge (by rfl) HyperEnv.Perm.merge_comm
      apply hP'.trans this.symm
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, h_pre_res, h_post_res⟩ := HyperEnv.Perm.extract_tensor_res
      hP hP'' hxx' hzx hzx' hyx hyx' hz_pre.2.1 hw_pre.2.1 hz_post.2.1 hw_post.2.1
      hzw hz_pre.2.2.2 hw_pre.2.2.1
    refine ⟨𝒢ₙ, Γₙ, Δₙ, C, D, hxx', ?_, ?_⟩
    · exact h_pre_res
    · have : 𝒢ₙ |ₕ [x' ∶ C :: Γₙ] |ₕ [x ∶ D :: Δₙ] ~ 𝒢ₙ |ₕ [x ∶ D :: Δₙ] |ₕ [x' ∶ C :: Γₙ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        apply HyperEnv.Perm.merge_comm
      exact h_post_res.trans this
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ₁, Γ₂, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Γ₁, Γ₂, A, B, hxx', ?_, hP'⟩
    exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ₁, Γ₂, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Γ₁, Γ₂, A, B, hxx', ?_, ?_⟩
    · exact hP1.symm.trans hP
    · exact hP2.symm.trans hP'

lemma TypingStepₘ_inv_parr_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {y y' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (y⸨y'⸩) 𝒟') :
  ∃ 𝒢ᵣ Γ A B,
    y ≠ y' ∧
    (𝒢 ~ 𝒢ᵣ |ₕ [y ∶ A ⅋ B :: Γ]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [y' ∶ A :: y ∶ B :: Γ]) := by
  generalize hl : (y⸨y'⸩ : Lbl) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl
  case parr =>
    expose_names
    obtain ⟨h1, h2⟩ := hl
    subst h1 h2
    simp [← ne_eq] at hy
    refine ⟨∅, Γ, A, B, hy.1.symm, by simp, by simp⟩
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Γ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥 |ₕ ℋ, Γ, A, B, hxx',  ?_, ?_⟩
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_exchange_rhs (HyperEnv.Perm.merge_comm) hP
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP'.trans HyperEnv.Perm.merge_comm
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Γ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒢_1 |ₕ 𝒥, Γ, A, B, hxx', ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP'
  case res 𝒥 𝒥' Γ Γ' Δ Δ' Q Q' A m l' L L' huniq huniq' z w hzw
    hz_pre hw_pre hz_post hw_post hlz hlw _ ih =>
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒦, Ξ, C, D, hxx', hP, hP'⟩ := ih
    simp only [Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.mem_union, not_or,
      Finset.notMem_singleton] at hlz hlw
    obtain ⟨hzx, hzx'⟩ := hlz
    obtain ⟨hyx, hyx'⟩ := hlw
    simp only [Finset.mem_union, not_or, and_assoc] at hz_pre hw_pre hz_post hw_post
    obtain ⟨𝒢ₙ, Γₙ, h_pre_res, h_post_res⟩ := HyperEnv.Perm.extract_parr_res
      hP hP' hxx' hzx hzx' hyx hyx' hz_pre.2.1 hw_pre.2.1 hz_post.2.1 hw_post.2.1
      hzw hz_pre.2.2.2 hw_pre.2.2.1
    refine ⟨𝒢ₙ, Γₙ, C, D, hxx', ?_, ?_⟩
    · exact h_pre_res
    · exact h_post_res
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Δ, A, B, hxx', ?_, hP'⟩
    exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Δ, A, B, hxx', ?_, ?_⟩
    · exact hP1.symm.trans hP
    · exact hP2.symm.trans hP'

lemma TypingStepₘ_inv_tensor_parr_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' y y' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ Δᵣ Ξᵣ A B C D,
    (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ] |ₕ [y ∶ C ⅋ D :: Ξᵣ]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξᵣ]) := by
  generalize hl : (x⟦x'⟧ |ₗ y⸨y'⸩) = l at hStep
  induction hStep <;> try simp [HasBracket.brack, HasParen.paren] at hl
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ := ih
    refine ⟨𝒢ₙ |ₕ ℋ, Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_rotate_rhs_right hP
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      apply HyperEnv.Perm_rotate_rhs_right
      rw [← HyperEnv.merge_assoc]
      exact hP'
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ := ih
    refine ⟨𝒢_1 |ₕ 𝒢ₙ , Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      rw [← HyperEnv.merge_assoc]
      exact hP
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      simp only [← HyperEnv.merge_assoc]
      exact hP'
  case syn ih1 ih2 =>
    expose_names ; clear ih1 ih2
    obtain ⟨hl1, hl2⟩ := hl
    subst hl1 hl2
    obtain ⟨𝒢ᵣ, Γ₁, Γ₂, A, B, hxx', hP_pre, hP_post⟩ := TypingStepₘ_inv_tensor_existential h₁
    obtain ⟨𝒢ᵣ', Δ, C, D, hyy', hP_pre', hP_post'⟩ := TypingStepₘ_inv_parr_existential h₂
    refine ⟨(𝒢ᵣ |ₕ 𝒢ᵣ'), Γ₁, Γ₂, Δ, A, B, C, D, ?_, ?_⟩
    · have hP_merge := HyperEnv.Perm.merge hP_pre hP_pre'
      have hP_trans : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ₁‚ Γ₂] |ₕ (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Δ]) ~
        𝒢ᵣ |ₕ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ₁‚ Γ₂] |ₕ [y ∶ C ⅋ D :: Δ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        simp only [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_left
        simp only [HyperEnv.merge_assoc]
        exact HyperEnv.Perm_merge_cancel_left_inv HyperEnv.Perm.merge_comm
      exact hP_merge.trans hP_trans
    · have hP_merge' := HyperEnv.Perm.merge hP_post hP_post'
      have hP_trans' : 𝒢ᵣ |ₕ [x ∶ B :: Γ₂] |ₕ [x' ∶ A :: Γ₁] |ₕ (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Δ]) ~
        𝒢ᵣ |ₕ 𝒢ᵣ' |ₕ [x ∶ B :: Γ₂] |ₕ [x' ∶ A :: Γ₁] |ₕ [y' ∶ C :: y ∶ D :: Δ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        conv_rhs => rw [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_left
        rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        exact HyperEnv.Perm.merge_comm
      exact  hP_merge'.trans hP_trans'
  case res ih =>
    expose_names
    subst hl
    obtain ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, A, B, C, D, hP_pre, hP_post⟩ := ih rfl
    simp [← ne_eq] at hlx hly
    simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
      at hx_pre hy_pre hx_post hy_post
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, h_pre_res, h_post_res⟩ :=
      HyperEnv.Perm.extract_tensor_parr_res
        hP_pre hP_post
        hlx.2.1 hlx.1 hlx.2.2.1 hlx.2.2.2
        hly.2.1 hly.1 hly.2.2.1 hly.2.2.2
        hneq
        hx_pre.2.1 hy_pre.2.1 hx_post.2.1 hy_post.2.1
        hx_pre.2.2.2 hy_pre.2.2.1
    refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, ?_⟩
    · exact h_pre_res
    · exact h_post_res
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ := ih
    refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, hP'⟩
    exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ := ih
    refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, ?_⟩
    · exact hP1.symm.trans hP
    · exact hP2.symm.trans hP'

lemma TypingStepₘ_inv_tensor_parr_source {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' y y' : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
  ∃ (C D E F : Types) (Γ₁ Γ₂ : Env),
    A = C ⨂ D ∧
    B = E ⅋ F ∧
    Γ ~ Γ₁‚ Γ₂ ∧
    𝒢' ~ 𝒢 |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁] |ₕ [y' ∶ E :: y ∶ F :: Δ] := by
  obtain ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, C, D, E, F, hP_pre, hP_post⟩ :=
    TypingStepₘ_inv_tensor_parr_existential hStep
  have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
  have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟
  simp [HyperEnv.PairwiseDisjoint_merge] at hpw
  have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1
  have hxLHS : ∃ Γ', Γ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Γ' ~ x ∶ C ⨂ D :: Γᵣ‚ Δᵣ := by
    have hxRHS : (x ∶ C ⨂ D :: Γᵣ‚ Δᵣ) ∈
      𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP_pre hxRHS
    simp [HasPerm.perm] at hPΞ
    simp at hΞ
    rcases hΞ with h1 | h2 | h3
    · exfalso
      exact (HyperEnv.not_mem_names_iff.mp hx𝒢 Ξ _ h1)
        ((List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ.symm).mp (by simp))
    · subst h2
      have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ).mpr (by simp)
      simp at hxin
      rcases hxin with ⟨rfl, rfl⟩ | h
      · refine ⟨(x ∶ (C ⨂ D) :: Γ), by simp, hPΞ⟩
      · exfalso ; exact hxΓ (Env.mem_pair_fst_in_names _ h)
    · subst h3
      have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ).mpr (by simp)
      simp at hxin
      rcases hxin with ⟨rfl, rfl⟩ | h
      · exfalso ; simp at hDΓΔ
      · exfalso ; exact hxΔ (Env.mem_pair_fst_in_names _ h)
  have hyLHS : ∃ Δ', Δ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Δ' ~ y ∶ E ⅋ F :: Ξᵣ := by
    have hyRHS : (y ∶ E ⅋ F :: Ξᵣ) ∈ 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP_pre hyRHS
    simp [HasPerm.perm] at hPΞ
    simp at hΞ
    rcases hΞ with h1 | h2 | h3
    · exfalso
      exact (HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ _ h1)
        ((List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ.symm).mp (by simp))
    · subst h2
      have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ).mpr (by simp)
      simp at hyin
      rcases hyin with ⟨rfl, rfl⟩ | h
      · exfalso ; simp at hDΓΔ
      · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
    · subst h3
      have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ).mpr (by simp)
      simp at hyin
      rcases hyin with ⟨rfl, rfl⟩ | h
      · refine ⟨(y ∶ (E ⅋ F) :: Δ), by simp, hPΞ⟩
      · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ h)
  simp at hxLHS hyLHS
  rcases hxLHS with ⟨Γ', hΓ', hPΓ'⟩
  rcases hyLHS with ⟨Δ', hΔ', hPΔ'⟩
  rcases hΓ' with h1 | h2 | h3
  · exfalso
    exact HyperEnv.not_mem_names_iff.mp
      hx𝒢 Γ' _ h1 ((List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ'.symm).mp (by simp))
  · subst h2
    rcases hΔ' with h4 | h5 | h6
    · exfalso
      exact HyperEnv.not_mem_names_iff.mp
        hy𝒢 Δ' _ h4 ((List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ'.symm).mp (by simp))
    · subst h5
      have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ').mpr (by simp)
      simp at hyin
      rcases hyin with ⟨rfl, rfl⟩ | h
      · exfalso ; simp at hDΓΔ
      · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
    · subst h6
      have hx_eq := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ').mpr (by simp)
      simp at hx_eq
      rcases hx_eq with ⟨rfl, rfl⟩ | hx_eq
      · have hy_eq := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ').mpr (by simp)
        simp at hy_eq
        rcases hy_eq with ⟨rfl, rfl⟩ | hy_eq
        swap ; · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ hy_eq)
        have hPΓ := List.Perm.cons_inv hPΓ'
        have hPΔ := List.Perm.cons_inv hPΔ'
        refine ⟨C, D, E, F, Γᵣ, Δᵣ, rfl, rfl, hPΓ, ?_⟩
        have hP1 : [x ∶ C ⨂ D :: Γ] ~ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] :=
          HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ)
        have hP2 : [y ∶ E ⅋ F :: Δ] ~ [y ∶ E ⅋ F :: Ξᵣ] :=
          HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ)
        have hP3 : 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γ] |ₕ [y ∶ E ⅋ F :: Δ] ~
          𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] :=
          HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP1) hP2
        have hP4 := hP_pre.trans hP3.symm
        apply HyperEnv.Perm_merge_cancel_right at hP4
        apply HyperEnv.Perm_merge_cancel_right at hP4
        have hP5 := hP_post.trans (HyperEnv.Perm.merge
          (HyperEnv.Perm.merge (HyperEnv.Perm.merge hP4.symm
            (HyperEnv.Perm.refl _)) (HyperEnv.Perm.refl _)) (HyperEnv.Perm.refl _))
        have hP6 : [y' ∶ E :: y ∶ F :: Ξᵣ] ~ [y' ∶ E :: y ∶ F :: Δ] :=
          HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ (List.Perm.cons _ hPΔ.symm))
        exact hP5.trans (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP6)
      · exfalso ; exact hxΓ (Env.mem_pair_fst_in_names _ hx_eq)
  · subst h3
    have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ').mpr (by simp)
    simp only [List.mem_cons] at hxin
    rcases hxin with ⟨rfl, rfl⟩ | h
    · simp [Env.disjoint] at hDΓΔ
    · exfalso ; exact hxΔ (Env.mem_pair_fst_in_names _ h)






lemma TypingStepₘ_inv_res_source {n n' : Nat} {P P' : Proc}
  {𝒢 ℋ : HyperEnv} {Γ Δ : Env} {A : Types} {x y : FPName} {l : Lbl}
  {𝒟' : n' ⊢ P' ∷ ℋ} (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])
  (hStep : TypingStepₘ 𝒟 l 𝒟') (hxl : x ∉ l.f ∪ l.i) (hyl : y ∉ l.f ∪ l.i) :
  ∃ (𝒢' : HyperEnv) (Γ' Δ' : Env), ℋ ~ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
  sorry











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
    exact TypingStepₘ.perm_hyper (𝒟' := 𝒟') hP.symm (by rfl) (TypingStepₘ.bot (hF := hxΓ))

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
    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names ∪ Δ.names := by simp [hF2, hyΓ, hyΔ, hF1]
    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons, Env.names_merge,
      Finset.mem_union, not_or] at hnd'
    have 𝒟y := Typing_tensor_all_fresh 𝒟' y hy
    · use [y ∶ A :: Γ] |ₕ [x ∶ B :: Δ], 𝒟y
      apply TypingStepₘ.perm_hyper hP.symm (by rfl)
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
    have hyΓ : y ∉ Γ.names := by intro hc ; simp [hc] at hfy
    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names := by simp [hF2, hyΓ, hF1]
    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd'
    have 𝒟y := Typing_parr_all_fresh 𝒟' y hy
    · use [y ∶ A :: x ∶ B :: Γ], 𝒟y
      apply TypingStepₘ.perm_hyper hP.symm (by rfl)
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
    apply TypingStepₘ.perm_hyper hP.symm (by rfl)
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
    apply TypingStepₘ.perm_hyper hP.symm (by rfl)
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
    · apply TypingStepₘ.perm_hyper hP.symm (by rfl)
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
    have hx_bound_t : x ∉ Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hxQf, hxℋ⟩, hxΓ⟩, hxΔ⟩
    have hy_bound_t : y ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hyQf, hyℋ⟩, hyΓ⟩, hyΔ⟩
    have hx_bound : x ∉ ({y} ∪ Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq]
      exact ⟨⟨⟨hxy, hxQf⟩, hxℋ⟩, hxΔ⟩
    have hy_bound : y ∉ (Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨hyQf, hyℋ⟩, hyΔ⟩
    have 𝒟xy := (Typing_res_all_fresh 𝒟' x y hx_bound_t hy_bound_t hxy)
    have ⟨_, _, hTS_t⟩ := ih 𝒟xy
    have ⟨hA, hB, hΓ, _⟩ := TypingStepₘ_inv_one_bot_source 𝒟xy hTS_t
    subst hA hΓ
    rw! [hB] at *
    have := (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    obtain ⟨𝒢', 𝒟'', hTS'⟩ := ih (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    have ⟨_, _, _, hP𝒢'⟩ := TypingStepₘ_inv_one_bot_source this hTS'
    refine ⟨𝒢', 𝒟'', ?_⟩
    apply TypingStepₘ.perm_hyper hP.symm hP𝒢'.symm
    · apply TypingStepₘ.one_bot (𝒢' := 𝒢') (huniq := 𝒟') (hx := hx_bound) (hy := hy_bound)
      · exact TypingStepₘ.perm_hyper (by rfl) hP𝒢' hTS'

  case tensor_parr Q Q' x x' y y' hxQf hyQf hx'Qf hy'Qf hxQ'f hyQ'f hx'Q'f hy'Q'f
    hxx' hxy hxy' hyx' hyy' hx'y' hPS ih =>
    generalize heq : (𝑣⸨$N,$N⸩ Q) = R at 𝒟
    induction 𝒟 generalizing Q <;> try contradiction
    case exchange_env hP ih' =>
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih' hxQf hyQf hx'Qf hy'Qf hPS ih heq
      expose_names
      refine ⟨𝒢_post, 𝒟_post, ?_⟩
      apply TypingStepₘ.perm_env hP hTS_post
    case exchange_hyper hP ih' =>
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih' hxQf hyQf hx'Qf hy'Qf hPS ih heq
      expose_names
      refine ⟨𝒢_post, 𝒟_post, ?_⟩
      apply TypingStepₘ.perm_hyper hP (by rfl) hTS_post
    case cut 𝒢 Γ Δ _ A m L 𝒟 ih' =>
      injection heq with hPQ
      subst hPQ
      have hNames := Typing.f_eq_names (Typing.cut L 𝒟)
      simp only [Proc.f_cut, HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge,
        HyperEnv.names_nil, Finset.union_empty] at hNames
      let hxQf_t := hxQf
      let hyQf_t := hyQf
      let hxQf_t' := hx'Qf
      let hyQf_t' := hy'Qf
      simp only [hNames, Finset.mem_union, not_or] at hxQf_t hyQf_t hxQf_t' hyQf_t'
      have hx_bound : x ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hxQf, hxQf_t⟩
      have hy_bound : y ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hyQf, hyQf_t⟩
      have hx'_bound : x' ∉ {y'} ∪ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq, and_assoc]
        exact ⟨hx'y', ⟨hx'Qf, hxQf_t'⟩⟩
      have hy'_bound : y' ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hy'Qf, hyQf_t'⟩
      have 𝒟xy := Typing_res_all_fresh 𝒟 x y hx_bound hy_bound hxy
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih 𝒟xy
      have ⟨C, D, E, F, Γ₁, Γ₂, hA, hA', hΓ, hP_post'⟩ :=
        TypingStepₘ_inv_tensor_parr_source 𝒟xy hTS_post
      subst hA
      let hA'_t := hA'
      simp [Types.dual] at hA'_t
      obtain ⟨hA'_t1, hA'_t2⟩ := hA'_t
      subst hA'_t1 hA'_t2

      have 𝒟xy_rw : m ⊢ Q⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ C ⨂ D :: Γ] |ₕ [y ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        exact 𝒟xy

      have hP_pre_rw : ∀ z w,
        𝒢 |ₕ [z ∶ C ⨂ D :: Γ] |ₕ [w ∶ Cᗮ ⅋ Dᗮ :: Δ] ~
        𝒢 |ₕ [z ∶ C ⨂ D :: Γ₁‚ Γ₂] |ₕ [w ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        intros z w
        exact HyperEnv.Perm_merge_cancel_right_inv (HyperEnv.Perm.merge (by rfl)
          (HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hΓ)))

      have step_rw : TypingStepₘ 𝒟xy_rw (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟_post := by
        apply TypingStepₘ.perm_hyper ?_ (by rfl) hTS_post
        rw [hA']

      have hTS_post' := TypingStepₘ.perm_hyper (hP_pre_rw x y) hP_post' step_rw
      have 𝒟_post' := Typing.exchange_hyper 𝒟_post hP_post'

      let L' := Q.f ∪ 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names
      have huinq_pre : ∀ x ∉ L', ∀ y ∉ L', x ≠ y →
        m ⊢ Q⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ C ⨂ D :: Γ₁‚ Γ₂] |ₕ [y ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        intros a ha b hb hab
        have hΓ_names : Γ.names = (Γ₁‚ Γ₂).names := Env.names_eq_of_perm hΓ
        have ha_bound : a ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
          simp only [L', hΓ_names, Finset.mem_union, not_or] at ⊢ ha
          exact ha
        have hb_bound : b ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
          simp only [L', hΓ_names, Finset.mem_union, not_or] at ⊢ hb
          exact hb

        have 𝒟ab := Typing_res_all_fresh 𝒟 a b ha_bound hb_bound hab

        have 𝒟ab_rw : m ⊢ Q⸨#a, #b⸩ ∷ 𝒢 |ₕ [a ∶ C ⨂ D :: Γ] |ₕ [b ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
          exact 𝒟ab
        exact Typing.exchange_hyper 𝒟ab (hP_pre_rw a b)

      have hL' : x ∉ L' ∧ y ∉ L' ∧ x' ∉ L' ∧ y' ∉ L' := by
        have hΓ_names : Γ.names = (Γ₁‚ Γ₂).names := Env.names_eq_of_perm hΓ
        simp only [L', ← hΓ_names, Finset.mem_union, not_or]
          at ⊢ hx_bound hy_bound hx'_bound hy'_bound
        exact ⟨⟨⟨⟨hxQf, hx_bound.1.1.2⟩, hx_bound.1.2⟩, hx_bound.2⟩,
               ⟨⟨⟨hyQf, hy_bound.1.1.2⟩, hy_bound.1.2⟩, hy_bound.2⟩,
               ⟨⟨⟨hx'Qf, hx'_bound.1.1.2⟩, hx'_bound.1.2⟩, hx'_bound.2⟩,
               ⟨⟨⟨hy'Qf, hy'_bound.1.1.2⟩, hy'_bound.1.2⟩, hy'_bound.2⟩⟩
      have huniq_post : ∀ z ∉ L', ∀ w ∉ L', z ≠ w → ∀ z' ∉ L',
        ∀ w' ∉ L', z' ≠ w' → z ≠ z' → z ≠ w' → w ≠ z' → w ≠ w' →
        m ⊢ Q'⸨2 | #z, #w⸩⸨#z', #w'⸩ ∷
          𝒢 |ₕ [z ∶ D :: Γ₂] |ₕ [z' ∶ C :: Γ₁] |ₕ [w' ∶ Cᗮ :: w ∶ Dᗮ :: Δ] := by
        intros z hzL w hwL hzw z' hz'L w' hw'L hz'w' hzz' hzw' hwz' hww'
        have hsubL' : 𝒢.names ∪ (Γ₂‚ Γ₁).names ∪ Δ.names ⊆ L' := by
          simp [L']
          rw [← Finset.union_assoc Γ₂.names Γ₁.names _, Finset.union_comm _ Γ₁.names,
            Finset.union_assoc]
          exact Finset.subset_union_right
        exact Typing_tensor_parr_post_all_fresh L' 𝒟_post' hL'.1 hL'.2.1 hL'.2.2.1 hL'.2.2.2
          hsubL' hxQ'f hyQ'f hx'Q'f hy'Q'f hxx' hxy hxy' hyx' hyy' hx'y' z hzL w hwL
          hzw z' hz'L w' hw'L hz'w' hzz' hzw' hwz' hww'

      have hP_rw : 𝒢 |ₕ [(Γ₁‚ Γ₂)‚ Δ] ~  𝒢 |ₕ [Γ‚ Δ] := by
        apply HyperEnv.Perm.merge (by rfl)
        rw [HyperEnv.Perm_singleton_singleton]
        apply List.Perm.append hΓ.symm (by rfl)

      have hTS_raw := TypingStepₘ.tensor_parr
        (L := L') (huniq := huinq_pre) (huniq' := huniq_post)
        (hx := hL'.1) (hy := hL'.2.1) (hneq := hxy)
        (hx' := hL'.2.2.1) (hy' := hL'.2.2.2) (hneq' := hx'y')
        (hxx' := hxx') (hxy' := hxy') (hyx' := hyx') (hyy' := hyy')
        (hxP := hxQf) (hyP := hyQf) (hx'P := hx'Qf) (hy'P := hy'Qf)
        (hxP' := hxQ'f) (hyP' := hyQ'f) (hx'P' := hx'Q'f) (hy'P' := hy'Q'f)
        hTS_post'
      have hTS_final := TypingStepₘ.perm_hyper hP_rw HyperEnv.Perm_refl hTS_raw
      exact ⟨_, _, hTS_final⟩

  case res Q Q' l' x y hxy hFx hFy hlx hly hES ih =>
    have ⟨A, Γ, Δ, ℋ, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    have hNames := Typing.f_eq_names 𝒟
    simp [HyperEnv.names_eq_of_perm hP] at hNames
    let hFx' := hFx
    let hFy' := hFy
    let hlx' := hlx
    let hly' := hly
    rw [hNames] at hFx' hFy'
    simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff,
      -Lbl.f, -Lbl.i] at hFx hFy hFx' hFy' hlx' hly'
    obtain ⟨hlxf, hlxi⟩ := hlx'
    obtain ⟨hlyf, hlyi⟩ := hly'
    obtain ⟨hxℋ, hxΓ, hxΔ, hxQ'f⟩ := hFx'
    obtain ⟨hyℋ, hyΓ, hyΔ, hyQ'f⟩ := hFy'
    have hx_bound : x ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hFx.1, hxℋ⟩, hxΓ⟩, hxΔ⟩
    have hy_bound : y ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hFy.1, hyℋ⟩, hyΓ⟩, hyΔ⟩
    have 𝒟xy := (Typing_res_all_fresh 𝒟' x y hx_bound hy_bound hxy)
    have ⟨𝒢xy', 𝒟xy', hTS_xy⟩ := ih 𝒟xy
    have ⟨𝒢', Γ', Δ', hP'⟩ := TypingStepₘ_inv_res_source 𝒟xy hTS_xy hlx hly
    have 𝒟xy' : n ⊢ Q'⸨#x, #y⸩ ∷ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] :=
      Typing.exchange_hyper 𝒟xy' hP'
    let L' := Q'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names
    have ⟨⟨hx𝒢', hxΓ', hxΔ'⟩, ⟨hy𝒢', hyΓ', hyΔ'⟩⟩ := Typing_res_fresh 𝒟xy'
    have hxL' : x ∉ L' := by simp [L', hxQ'f, hx𝒢', hxΓ', hxΔ']
    have hyL' : y ∉ L' := by simp [L', hyQ'f, hy𝒢', hyΓ', hyΔ']
    have hEnv : 𝒢'.names ∪ Γ'.names ∪ Δ'.names ⊆ L' := by
      intro a ha
      simp only [L', Finset.mem_union] at ⊢ ha
      rcases ha with h1 | hΔ'
      · rcases h1 with h𝒢' | hΓ'
        · left ; left ; right ; exact h𝒢'
        · left ; right ; exact hΓ'
      · right ; exact hΔ'
    have 𝒟'_post_L' : ∀ z ∉ L', ∀ w ∉ L', z ≠ w →
      n ⊢ Q'⸨#z, #w⸩ ∷ 𝒢' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'] := by
      apply Typing_res_post_all_fresh L' 𝒟xy' hxL' hyL' hxQ'f hyQ'f hEnv hxy
    have hTS_xy' : TypingStepₘ 𝒟xy l' 𝒟xy' :=
      TypingStepₘ.perm_hyper (by rfl) hP' hTS_xy
    refine ⟨𝒢' |ₕ [Γ'‚ Δ'], Typing.cut L' 𝒟'_post_L', ?_⟩
    apply TypingStepₘ.perm_hyper hP.symm HyperEnv.Perm_refl
    exact TypingStepₘ.res (L := L) (L' := L') (huniq := 𝒟') (huniq' := 𝒟'_post_L')
      hxy hx_bound hy_bound hxL' hyL' hlx hly hTS_xy'

theorem subject_reductionₘ {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
  (𝒟 : Typing n P 𝒢) (hPS : ProcStepₘ P l P') :
  ∃ 𝒢', EnvStepₘ 𝒢 l 𝒢' ∧ (Typing n P' 𝒢') := by
  obtain ⟨𝒢', 𝒟', hTS⟩ := typability_subject_reductionₘ 𝒟 hPS
  have hES := session_fidelity_envₘ hTS
  exact ⟨𝒢', hES, 𝒟'⟩



-- TODO: Move ProcStep, EnvStep, and Typing and HyperEnv lemmas to respective files

-- TODO: Prove Session fidelity, erasure, type preservation, Session fidelity for πLL


-- FIXME: Typing_preserves_proc_congr
-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere




-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs
-- FIXME: Find different syntax for open?
-- FIXME: Prove name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }

-- FIXME: Move everything related to HyperEnv.Perm to a separate file? Or at least organize
-- definition and lemma ordering a bit.

-- TODO: Change lemma naminig and dot notation interactions to follow standard pattern
-- TODO: Change HyperEnv.Nodup def to match Env
-- TODO: Change the names of the HyperEnv rotate left / right lemmas to match what they do
-- TODO: Edit files to follow the new linters lean has added

/- TODO:
  - Remove _source variants of TypingStep inversion lemmas
    and their respective extract perm and existential variants (not existential')
  - But also rename existential' to something else
-/

/- TODO:
  - Maybe remove all_fresh from one_bot signature and make it like tensor_parr and
  do inline induction instead.
-/
