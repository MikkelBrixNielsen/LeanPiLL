import PiLL.Model.Judgement.Substitution.Names
import PiLL.Model.Judgement.Properties.Names
import PiLL.Model.Judgement.Properties.Linearity
import PiLL.Model.Processes.Fresh

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
  rw [Typing_f_eq_names 𝒟]
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
  Typing n (𝑣⸨•,•⸩ (𝑣⸨•,•⸩ P')) (𝒢 |ₕ [Γ‚ (Δ‚ Ξ)]) :=
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
