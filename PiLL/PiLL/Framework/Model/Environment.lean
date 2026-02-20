import PiLL.Framework.Model.Process

-- --------------------------------------- ENVIRONMENTS ---------------------------------------

-- abbrev Env := Finset (PName × Types)

-- abbrev EmptyEnv : Env := ∅

-- def Env.mk (x : PName) (A : Types) : Env := {(x, A)}
-- infixr:86 " ∶ " => Env.mk

-- -- NOTE: It's a set so linear by definition
-- -- def Env.linear (Δ : Env) : Prop :=
--   -- (Δ.image Prod.fst).card = Δ.card

-- def Env.names (Δ : Env) : Finset (PName) :=
--   (Δ.image Prod.fst)

-- @[simp] def Env.disjoint (Δ Γ : Env) : Prop :=
--   Disjoint Δ.names Γ.names

-- noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
--   -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
--   (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

-- notation Δ "⸨" x "⸩ₑ" => Env.lookup Δ x

-- -- Order independent equality for environments
-- @[simp] def Env.Eq (Δ Γ : Env) : Prop :=
--   ∀ x : (PName), Δ⸨x⸩ₑ = Γ⸨x⸩ₑ

-- notation Δ " =ₑ " Γ => Env.Eq Δ Γ

-- -- Eq reflexivity
-- @[simp] theorem Env.Eq_refl (Δ : Env) : Δ =ₑ Δ :=
--   fun _ => rfl

-- -- Eq symmetry
-- theorem Env.Eq_symm (Δ Γ : Env) (h : Δ =ₑ Γ) : Γ =ₑ Δ :=
--   fun x => (h x).symm

-- -- Eq transitivity
-- theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Δ =ₑ Γ) (h₂ : Γ =ₑ Ε) : Δ =ₑ Ε :=
--   fun x => Eq.trans (h₁ x) (h₂ x)

-- instance : Equivalence Env.Eq :=
-- ⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

-- def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

-- infixl:85 "‚ " => Env.merge

-- -- Merge identity
-- @[simp] theorem Env.merge_unitR (Δ : Env) : Δ‚ ∅ = Δ := by
--   simp [Env.merge]

-- @[simp] theorem Env.merge_unitL (Δ : Env) : ∅‚ Δ = Δ := by
--   simp [Env.merge]

-- -- Merge commutivity
-- theorem Env.merge_comm (Δ Γ : Env) : Δ‚ Γ = Γ‚ Δ := by
--   simp [Env.merge, Finset.union_comm]

-- -- Merge associativity
-- theorem Env.merge_assoc (Δ Γ Ε : Env) : Δ‚ Γ‚ Ε = Δ‚ (Γ‚ Ε) := by
--   simp [Env.merge]

-- lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
--   (Γ‚ Δ)‚ Ξ = (Γ‚ Ξ)‚ Δ := by
--   rw [Env.merge_comm, ←Env.merge_assoc]
--   conv => lhs ; lhs ; rw [Env.merge_comm]

-- lemma Env.merge_move_last_two_left (Γ Δ Ξ Ε : Env) :
--   Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ε‚ Δ‚ Ξ := by
--   rw [Env.merge_swap_last, Env.merge_swap_last Γ Δ Ε]

-- lemma Env.merge_move_second_two_right (Γ Δ Ξ Ε : Env) :
--   Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ξ‚ Ε‚ Δ := by
--   rw [Env.merge_swap_last Γ Δ Ξ, Env.merge_swap_last]

-- def Env.serverUsable (Γ : Env) : Prop :=
--   ∀p, p ∈ Γ → (p.snd).isServerUsable

-- prefix:max "?ₑ" => Env.serverUsable

-- def Env.freeTypes (Γ : Env) : Finset TVar :=
--   Γ.biUnion (fun (_, A) => A.freeTypes)

-- notation "ft(" Γ ")ₑ" => Env.freeTypes Γ

-- def Env.substName (Γ : Env) (x z : PName) : Env :=
--   Γ.image (fun (n, T) => if n = z then (x, T) else (n, T))

-- instance : HasSubst Env PName PName where subst := Env.substName

-- def Env.substTypes (Γ : Env) (A : Types) (X : TVar) : Env :=
--   Γ.image (fun (n, T) => (n, T.subst A X))

-- instance : HasSubst Env Types TVar where subst := Env.substTypes

-- @[simp] lemma Env.serverUsable_substName (Γ : Env) (x z : PName) (h : ?ₑΓ) :
--   ?ₑ(Γ{x // z}) := by
--   simp only [Env.serverUsable, HasSubst.subst, Env.substName] at *
--   simp only [Finset.forall_mem_image, apply_ite] at *
--   simp at *
--   exact h

-- @[simp] lemma Env.serverUsable_substTypes (Γ : Env) (A : Types) (X : TVar) (h : ?ₑΓ) :
--   ?ₑ(Γ{A // X}) := by
--   simp only [Env.serverUsable, HasSubst.subst, Env.substTypes] at *
--   intro p hp
--   rcases Finset.mem_image.mp hp with ⟨op, hom, heq⟩
--   have hou := h op hom
--   simp [← heq] at *
--   apply Types.isServerUsable_subst
--   exact hou

-- lemma Env.names_substName (Γ : Env) (x z : PName) :
--   Γ{x // z}.names = Γ.names.image (fun n => if n = z then x else n) := by
--   simp only [Env.names, HasSubst.subst, Env.substName, Finset.image_image]
--   apply Finset.image_congr
--   intro ⟨n, t⟩ _
--   dsimp
--   split_ifs <;> rfl

-- @[simp] lemma Env.substName_eq_self_of_not_mem {Γ : Env} {x z : PName}
--   (h : z ∉ Γ.names) : Γ{x // z} = Γ := by
--   simp only [HasSubst.subst, Env.substName]
--   conv_rhs => rw [← Finset.image_id (s := Γ)]
--   apply Finset.image_congr
--   intro p hpΓ
--   simp_all [Env.names]
--   intro a
--   subst a
--   simp_all

-- @[simp] lemma Env.names_singleton (x : PName) (A : Types) :
--   (x ∶ A).names = {x} := by
--   simp [Env.names, Env.mk]

-- @[simp] lemma Env.names_empty : (∅ : Env).names = ∅ := by simp [Env.names]

-- @[simp] lemma Env.names_distributes (Γ Δ : Env) :
--   (Γ‚ Δ).names = Γ.names ∪ Δ.names := by
--     simp only [Env.names, ← Finset.image_union]
--     rfl

-- @[simp] lemma Env.substName_empty (x z : PName) :
--   (∅ : Env){x // z} = ∅ := by
--   simp only [HasSubst.subst, Env.substName, Finset.image_empty]

-- @[simp] lemma Env.substName_distributes (Γ Δ : Env) (x z : PName) :
--   (Γ‚ Δ){x // z} = Γ{x // z}‚ Δ{x // z} := by
--   simp [HasSubst.subst, Env.substName, Env.merge, Finset.image_union]

-- @[simp] lemma Env.substName_singleton (x y z : PName) (A : Types) :
--   (y ∶ A){x // z} = (if y = z then x else y) ∶ A := by
--   simp only [HasSubst.subst, Env.substName, Env.mk, Finset.image_singleton]
--   split <;> rfl

-- @[simp] lemma Env.not_mem_substName_intro {Γ : Env} {x y z : PName}
--   (hnΓ : y ∉ Γ.names) (hneq : y ≠ x) : y ∉ (Γ{x // z}).names := by
--   intro h_contra
--   simp [HasSubst.subst, Env.substName, Env.names] at h_contra
--   rcases h_contra with ⟨T, pn, h⟩
--   split_ifs at h
--   · simp_all
--   · rcases h with ⟨b, hΓ, heq⟩
--     simp_all [Env.names]

-- @[simp] lemma Env.ft_substName_eq_self (Γ : Env) (x z : PName) :
--   ft(Γ{x // z})ₑ = ft(Γ)ₑ := by
--   simp only [HasSubst.subst, Env.freeTypes, Env.substName]
--   rw [Finset.image_biUnion]
--   exact Finset.biUnion_congr rfl (by intro p hin ; split <;> rfl)

-- @[simp] lemma Env.substName_preserves_disjoint {Γ Δ : Env} {x z : PName}
--   (hDisj : Γ.disjoint Δ) (hFresh : x ∉ Γ.names ∧ x ∉ Δ.names) :
--   Γ{x // z}.disjoint Δ{x // z} := by
--   dsimp only [Env.disjoint]
--   simp only [Env.names_substName]
--   apply Finset.disjoint_image_substName
--   · exact hDisj
--   · exact hFresh.1
--   · exact hFresh.2

-- @[simp] lemma Env.substTypes_empty {A : Types} {X : TVar} :
--   (∅ : Env){A // X} = (∅ : Env) := by rfl

-- @[simp] lemma Env.substTypes_singleton {x : PName} {T A : Types} {X : TVar} :
--   (x ∶ T){A // X} = x ∶ T{A// X} := by
--   simp only [HasSubst.subst, Env.substTypes, Env.mk, Finset.image_singleton]

-- @[simp] lemma Env.substTypes_distributes {Γ Δ : Env} {A : Types} {X : TVar} :
--   (Γ‚ Δ){A // X} = Γ{A // X}‚ Δ{A // X} := by
--   simp only [HasSubst.subst, Env.substTypes, Env.merge, Finset.image_union]

-- @[simp]
-- lemma Env.names_substTypes {Γ : Env} {A : Types} {X : TVar} :
--   (Γ{A // X}).names = Γ.names := by
--   simp only [Env.names, Env.substTypes, HasSubst.subst, Finset.image_image]
--   apply Finset.image_congr
--   intro ⟨n, T⟩ _
--   rfl

-- @[simp] lemma Env.substTypes_preserves_disjoint {Γ Δ : Env} {A : Types} {X : TVar} :
--   Γ{A // X}.disjoint Δ{A // X} = Γ.disjoint Δ := by
--   simp only [Env.disjoint, Env.names_substTypes]

-- @[simp] lemma Env.substTypes_eq_self_of_not_mem {Γ : Env} {A : Types} {X : TVar}
--   (h : X ∉ ft(Γ)ₑ) : Γ{A // X} = Γ := by
--   simp only [HasSubst.subst, Env.substTypes]
--   conv_rhs => rw [← Finset.image_id (s := Γ)]
--   apply Finset.image_congr
--   intro ⟨n, T⟩ hin
--   simp
--   apply Types.subst_eq_self
--   simp only [Env.freeTypes, Finset.mem_biUnion, not_exists, not_and] at h
--   exact h (n, T) hin

-- @[simp] lemma Env.not_mem_ft_substTypes {Γ : Env} {A : Types} {X Y : TVar} {hΓ : Y ∉ ft(Γ)ₑ}
--   {hA : Y ∉ A.freeTypes} {hneq : Y ≠ X} : Y ∉ ft(Γ{A // X})ₑ := by
--   simp only [HasSubst.subst, Env.substTypes, Env.freeTypes, Finset.mem_biUnion,
--     not_exists, not_and]
--   intro p hp
--   rcases Finset.mem_image.mp hp with ⟨op, hom, heq⟩
--   subst heq
--   apply Types.not_mem_ft_subst
--   · rw [Env.freeTypes] at hΓ
--     simp only [Finset.mem_biUnion, not_exists, not_and] at hΓ
--     exact hΓ op hom
--   · exact hA
--   · exact hneq

-- @[simp] lemma Env.substTypes_mk {x : PName} {T A : Types} {X : TVar} :
--   (x ∶ T){A // X} = x ∶ T.subst A X := by
--   simp only [HasSubst.subst, Env.substTypes, Env.mk, Finset.image_singleton]

-- @[simp] lemma Env.freeTypes_empty :
--   ft(∅)ₑ = ∅ := by simp only [Env.freeTypes, Finset.biUnion_empty]

-- @[simp] lemma Env.freeTypes_singleton {x : PName} {A : Types} :
--   ft((x ∶ A : Env))ₑ = A.freeTypes := by
--   simp only [Env.freeTypes, Env.freeTypes, Env.mk, Finset.singleton_biUnion]

-- @[simp] lemma Env.freeTypes_distributes {Γ Δ : Env} :
--    (ft(Γ‚ Δ)ₑ) = (ft(Γ)ₑ ∪ ft(Δ)ₑ) := by
--    simp only [Env.merge, Env.freeTypes, Finset.biUnion_union]

-- @[simp] lemma Env.freeTypes_notMem_merge {Γ Δ : Env} {X : TVar} :
--    (X ∉ ft(Γ‚ Δ)ₑ) = (X ∉ ft(Γ)ₑ ∧ X ∉ ft(Δ)ₑ) := by
--    simp only [Env.freeTypes_distributes, Finset.notMem_union]

-- ------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

-- abbrev HyperEnv := Finset (Env)

-- abbrev EmptyHyperEnv : HyperEnv := ∅

-- instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

-- -- def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
-- --   ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

-- -- FIXME: Relevance?
-- -- def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
--   -- ∀ Δ ∈ 𝒢, Δ.linear ∧                            -- ensure each env is linear
--   -- pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

-- def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
--   𝒢.biUnion Env.names

-- -- Lookup method for finding the type of a name in the hyperenvironment
-- noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
--   (𝒢.toList.find? (fun Δ => Δ⸨x⸩ₑ ≠ none)) >>= fun Δ  => Δ⸨x⸩ₑ

-- notation:60 𝒢 "⸨" x "⸩ₕ" => HyperEnv.lookup 𝒢 x

-- def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
--   -- 1. ensure both hyperenvs are lienar (Linear by definition of Finset)
--   -- 2. ensure disjoint env names
--   -- 3. ensure no duplicate definitions across hyperenvs
--     -- s.t. an unambigous lookup in the individual hyperenvs
--     -- yields an unambigous lookupin the merged hyperenv
--     -- i.e. the intersection of their defined names is empty
--   -- 𝒢.linear ∧ ℋ.linear ∧
--   -- (𝒢 ∩ ℋ).card = 0 ∧
--   -- (𝒢.names ∩ ℋ.names).card = 0
--   Disjoint 𝒢.names ℋ.names

-- -- Order independent equality for hyper-environments
-- @[simp] def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
--   -- (1) 𝒢 and ℋ must define the same names
--   -- (2) The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
--   HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
--   ∀ x ∈ HyperEnv.names 𝒢, 𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ

-- notation 𝒢 " =ₕ " ℋ => HyperEnv.Eq 𝒢 ℋ

-- -- Eq reflexivity
-- @[simp] theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : 𝒢 =ₕ 𝒢 := by
--   simp

-- -- Eq symmetry
-- theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : 𝒢 =ₕ ℋ) : ℋ =ₕ 𝒢 := by
--   rcases h with ⟨h_names, h_vals⟩
--   refine ⟨h_names.symm, ?vals⟩
--   intro x hx
--   rw [h_names] at h_vals
--   apply (h_vals x hx).symm

-- -- Eq transitivity
-- theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : 𝒢 =ₕ ℋ) (h₂ : ℋ =ₕ 𝒦) :
--   𝒢 =ₕ 𝒦 := by
--   rcases h₁ with ⟨h₁_names, h₁_vals⟩
--   rcases h₂ with ⟨h₂_names, h₂_vals⟩
--   refine ⟨?names, ?vals⟩
--   · rw [h₁_names, h₂_names]
--   · intro x hx
--     have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
--     calc
--       𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ := h₁_vals x hx
--       _          = 𝒦⸨x⸩ₕ := h₂_vals x hxH

-- instance : Equivalence HyperEnv.Eq :=
-- ⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

-- abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

-- infixl:55 " |ₕ " => HyperEnv.merge

-- -- Merge identity
-- @[simp] theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

-- @[simp] theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

-- -- Merge commutative
-- theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : 𝒢 |ₕ ℋ = ℋ |ₕ 𝒢 := by
--   simp [Finset.union_comm]

-- -- Merge associativity
-- theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) : (𝒢 |ₕ ℋ) |ₕ 𝒦 = 𝒢 |ₕ (ℋ |ₕ 𝒦) := by
--   simp

-- def HyperEnv.freeTypes (𝒢 : HyperEnv) : Finset TVar :=
--   𝒢.biUnion (fun Γ => ft(Γ)ₑ)

-- notation "ft(" 𝒢 ")ₕ" => HyperEnv.freeTypes 𝒢

-- def HyperEnv.substName (𝒢 : HyperEnv) (x z : PName) : HyperEnv :=
--   𝒢.image (fun Γ => Γ{x // z})

-- instance : HasSubst HyperEnv PName PName where subst := HyperEnv.substName

-- def HyperEnv.substTypes (𝒢 : HyperEnv) (A : Types) (X : TVar) : HyperEnv :=
--   𝒢.image (fun Γ => Γ.substTypes A X)

-- instance : HasSubst HyperEnv Types TVar where subst := HyperEnv.substTypes

-- @[simp] lemma HyperEnv.names_singleton (Γ : Env) :
--   ({Γ} : HyperEnv).names = Γ.names := by
--   simp [HyperEnv.names, Env.names, Finset.singleton_biUnion]

-- @[simp] lemma HyperEnv.names_distributes (𝒢 ℋ : HyperEnv) :
--   (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
--   simp only [HyperEnv.names, Finset.biUnion_union]

-- @[simp] lemma HyperEnv.names_empty : (∅ : HyperEnv).names = ∅ := by simp [HyperEnv.names]

-- lemma HyperEnv.substName_merge (𝒢 ℋ : HyperEnv) (x z : PName) :
--   𝒢{x // z} |ₕ ℋ{x // z} = (𝒢 |ₕ ℋ){x // z} := by
--   simp [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]

-- lemma HyperEnv.names_substName (𝒢 : HyperEnv) (x z : PName) :
--   𝒢{x // z}.names = 𝒢.names.image (fun n => if n = z then x else n) := by
--   simp only [HyperEnv.names, HasSubst.subst, HyperEnv.substName]
--   rw [Finset.biUnion_image]
--   rw [Finset.image_biUnion]
--   apply Finset.biUnion_congr
--   · rfl
--   · intro Γ _
--     apply Env.names_substName

-- @[simp] lemma HyperEnv.substName_preserves_disjoint (𝒢 ℋ : HyperEnv) (x z : PName)
--   (hDisj : 𝒢.disjoint ℋ) (hFresh : x ∉ 𝒢.names ∧ x ∉ ℋ.names) :
--   𝒢{x // z}.disjoint ℋ{x // z} := by
--   dsimp only [HyperEnv.disjoint]
--   simp only [HyperEnv.names_substName]
--   apply Finset.disjoint_image_substName
--   · exact hDisj
--   · exact hFresh.1
--   · exact hFresh.2

-- lemma HyperEnv.substName_eq_self_of_not_mem (𝒢 : HyperEnv) (x z : PName)
--   (h : z ∉ 𝒢.names) : 𝒢{x // z} = 𝒢 := by
--   simp only [HasSubst.subst, HyperEnv.substName, Env.substName]
--   conv_rhs => rw [← Finset.image_id (s := 𝒢)]
--   apply Finset.image_congr
--   intro Γ hΓ𝒢
--   simp
--   apply Env.substName_eq_self_of_not_mem
--   simp_all [HyperEnv.names]

-- @[simp] lemma HyperEnv.substName_empty (x z : PName) :
--   (∅ : HyperEnv){x // z} = ∅ := by
--   simp only [HasSubst.subst, HyperEnv.substName, Finset.image_empty]

-- @[simp] lemma HyperEnv.substName_singleton (Γ : Env) (x z : PName) :
--   ({Γ} : HyperEnv){x // z} = Γ{x // z} := by
--   simp only [HasSubst.subst, HyperEnv.substName, Finset.image_singleton]

-- @[simp] lemma HyperEnv.substName_distributes (𝒢 ℋ : HyperEnv) (x z : PName) :
--   (𝒢 |ₕ ℋ){x // z} = 𝒢{x // z} |ₕ ℋ{x // z} := by
--   simp only [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]

-- @[simp] lemma HyperEnv.not_mem_substName_intro {𝒢 : HyperEnv} {x y z : PName}
--   (hnΓ : y ∉ 𝒢.names) (hneq : x ≠ y) : y ∉ (𝒢{x // z}).names := by
--   intro h_contra
--   simp [HasSubst.subst, HyperEnv.substName, HyperEnv.names,
--     Env.substName, Env.names] at h_contra
--   rcases h_contra with ⟨Γ, h1⟩
--   rcases h1 with ⟨hΓ𝒢, T, on, oT, hΓ, heq⟩
--   split_ifs at heq with hz
--   · simp at heq
--     rw [heq.1] at hneq
--     contradiction
--   · simp_all [HyperEnv.names, Env.names]

-- @[simp] lemma HyperEnv.substTypes_empty {A : Types} {X : TVar} :
--   (∅ : HyperEnv){A // X} = (∅ : HyperEnv) := by rfl

-- @[simp] lemma HyperEnv.substTypes_singleton {Γ : Env} {A : Types} {X : TVar} :
--   ({Γ} : HyperEnv){A // X} = Γ{A // X} := by
--   simp only [HasSubst.subst, HyperEnv.substTypes, Finset.image_singleton]

-- @[simp] lemma HyperEnv.substTypes_distributes {𝒢 ℋ : HyperEnv} {A : Types} {X : TVar} :
--   (𝒢 |ₕ ℋ){A // X} = 𝒢{A // X} |ₕ ℋ{A // X} := by
--   simp only [HasSubst.subst, HyperEnv.substTypes, HyperEnv.merge, Finset.image_union]

-- @[simp] lemma HyperEnv.names_substTypes {𝒢 : HyperEnv} {A : Types} {X : TVar} :
--   (𝒢{A // X}).names = 𝒢.names := by
--   simp only [HyperEnv.names, HyperEnv.substTypes, HasSubst.subst]
--   rw [Finset.image_biUnion]
--   exact Finset.biUnion_congr rfl (by intro Γ _ ; apply Env.names_substTypes)

-- @[simp] lemma HyperEnv.substTypes_preserves_disjoint {𝒢 ℋ : HyperEnv} {A : Types} {X : TVar} :
--   𝒢{A // X}.disjoint ℋ{A // X} = 𝒢.disjoint ℋ := by
--   simp only [HyperEnv.disjoint, HyperEnv.names_substTypes]

-- @[simp] lemma HyperEnv.freeTypes_empty :
--   ft(∅)ₕ = ∅ := by simp only [HyperEnv.freeTypes, Finset.biUnion_empty]

-- @[simp] lemma HyperEnv.freeTypes_singleton {Γ : Env} :
--   ft(({Γ} : HyperEnv))ₕ = ft(Γ)ₑ := by
--   simp only [HyperEnv.freeTypes, HyperEnv.freeTypes, Finset.singleton_biUnion]

-- @[simp] lemma HyperEnv.freeTypes_distributes {𝒢 ℋ : HyperEnv} :
--    (ft(𝒢 |ₕ ℋ)ₕ) = (ft(𝒢)ₕ ∪ ft(ℋ)ₕ) := by
--    simp only [HyperEnv.merge, HyperEnv.freeTypes, Finset.biUnion_union]

-- @[simp] lemma HyperEnv.freeTypes_notMem_merge {𝒢 ℋ : HyperEnv} {X : TVar} :
--    (X ∉ ft(𝒢 |ₕ ℋ)ₕ) = (X ∉ ft(𝒢)ₕ ∧ X ∉ ft(ℋ)ₕ) := by
--    simp only [HyperEnv.freeTypes_distributes, Finset.notMem_union]

-- lemma HyperEnv.mem_implies_names_subset_self {𝒢 : HyperEnv} {Γ : Env} (h : Γ ∈ 𝒢) :
--   Γ.names ⊆ 𝒢.names := by
--   simp [HyperEnv.names, Env.names]
--   apply Finset.subset_biUnion_of_mem (fun E => Env.names E) h

-- lemma HyperEnv.merge_swap_last (𝒢 ℋ 𝒥 : HyperEnv) : 𝒢 |ₕ ℋ |ₕ 𝒥 = 𝒢 |ₕ 𝒥 |ₕ ℋ := by
--   rw [HyperEnv.merge_assoc, HyperEnv.merge_comm _ 𝒥, ← HyperEnv.merge_assoc]

-- def HyperEnv.PairwiseDisjoint (𝒢 : HyperEnv) : Prop :=
--   ∀ Γ ∈ 𝒢, ∀ Δ ∈ 𝒢, Γ ≠ Δ → Γ.disjoint Δ

-- lemma HyperEnv.merge_move_second_two_right (𝒢 ℋ ℐ 𝒥 : HyperEnv) :
--   𝒢 |ₕ ℋ |ₕ ℐ |ₕ 𝒥 = 𝒢 |ₕ ℐ |ₕ 𝒥 |ₕ ℋ := by
--   rw [HyperEnv.merge_swap_last 𝒢 ℋ ℐ, HyperEnv.merge_swap_last (𝒢 |ₕ ℐ) ℋ 𝒥]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Elem := (FPName × Types)

abbrev Elem.mk (x : FPName) (A : Types) : Elem := (x, A)
infixr:68 " ∶ " => Elem.mk

infixl:50 " ~ " => List.Perm

abbrev Env := List Elem

def Env.names (Γ : Env) : Finset FPName :=
  (Γ.map Prod.fst).toFinset

@[simp] def Env.disjoint (Δ Γ : Env) : Prop :=
  Disjoint Δ.names Γ.names

def Env.serverUsable (Γ : Env) : Prop :=
  ∀p, p ∈ Γ → (p.snd).isServerUsable
prefix:max "?ₑ" => Env.serverUsable

def Env.freeTypes (Γ : Env) :=
  Γ.foldl (fun acc (_, A) => acc ∪ A.freeTypes) ∅
notation "ft(" Γ ")ₑ" => Env.freeTypes Γ

def Env.lc (k : Nat) (Γ : Env) : Prop :=
  ∀ x A, (x, A) ∈ Γ → A.lc k

-- d : Depth shift should be applied
-- c : Correction / how much to shift
def Env.shiftTypes (d c : Nat) (Γ : Env) : Env :=
  Γ.map (fun (x, A) => (x, A.shift d c))

instance : HasShiftTypes Env where shift Γ d c := Env.shiftTypes d c Γ

def Env.substNames (Γ : Env) (R T : FPName) : Env :=
  Γ.map (fun (x, A) => if x == T then (R, A) else (x, A))

instance : HasSubst Env FPName FPName where subst := Env.substNames

def Env.substTypes (Γ : Env) (A : Types) (k : Nat) : Env :=
  Γ.map (fun (x, B) => (x, B.subst A k))

instance : HasSubst Env Types Nat where subst := Env.substTypes

abbrev Env.merge (Γ Δ : Env) : Env := Γ ++ Δ
infixr:69 "‚ " => Env.merge

lemma Env.merge_unitL (Γ : Env) : ∅‚ Γ = Γ := by simp

lemma Env.merge_unitR (Γ : Env) : Γ‚ ∅ = Γ := by simp

lemma Env.merge_comm (Γ Δ : Env) : List.Perm (Γ‚ Δ) (Δ‚ Γ) := by
  exact List.perm_append_comm

lemma Env.merge_assoc (Γ Δ Ξ : Env) : Γ‚ Δ‚ Ξ = Γ‚ (Δ‚ Ξ) := by
  simp [Env.merge]

lemma Env.merge_rotate_left (Γ : Env) (x : FPName × Types) :
  (x :: Γ).Perm (Γ‚ [x]) := by
  symm ; apply List.perm_append_singleton

lemma Env.merge_swap (Γ : Env) (x y : FPName × Types) :
  List.Perm (x :: y :: Γ) (y :: x :: Γ) := by
  symm ; simpa using List.Perm.swap x y Γ

lemma Env.names_eq_of_perm {Γ Δ : Env} (h : Γ ~ Δ) :
  Γ.names = Δ.names := by
  dsimp [Env.names]
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset]
  apply List.Perm.mem_iff
  apply List.Perm.map _ h

lemma Env.mem_of_disjoint_le_bot {Γ Δ : Env} {x : Finset FPName}
  (hΓΔ : Disjoint Γ.names Δ.names) (hxΓ : x ≤ Γ.names) (hxΔ : x ≤ Δ.names) :
  x ≤ ⊥ := by
  exact le_trans (le_inf hxΓ hxΔ) (Disjoint.le_bot hΓΔ)

lemma Env.lc_shift_inv {n k : Nat} {Γ : Env} :
  (Γ⁺ᵗ).lc (n + k + 1) ↔ Γ.lc (n + k) := by
  simp [Env.lc, HasShiftTypes.shift, Env.shiftTypes]
  constructor
  all_goals (
    intro h x A hin
    specialize h x A hin
    have := Types.lc_shift_inv_0 (A := A) (n := n + k)
    simp_all
  )

lemma Env.lc_shift_inv_0 {n : Nat} {Γ : Env} :
  (Γ⁺ᵗ).lc (n + 1) ↔ Γ.lc n := Env.lc_shift_inv (k := 0)

lemma Env.lc_cons {n : Nat} {x : FPName} {A : Types} {Γ : Env} :
  Env.lc n ((x, A) :: Γ) ↔ A.lc n ∧ Γ.lc n := by
  unfold Env.lc
  constructor
  · intro h
    constructor
    · apply h x A
      simp
    · intro y B hΓ
      apply h y B
      simp [hΓ]
  · rintro ⟨h1, h2⟩ y B hMem
    cases hMem
    · exact h1
    · rename_i hΓ
      apply h2 y B hΓ

lemma Env.lc_singleton {n : Nat} {x : FPName} {A : Types} :
  Env.lc n ([x ∶ A]) ↔ A.lc n := by simp_all [Env.lc]

lemma Env.lc_append {n : Nat} {Γ Δ : Env} :
  (Γ‚ Δ).lc n ↔ Γ.lc n ∧ Δ.lc n := by
  simp [Env.lc, Env.merge]
  constructor
  · intro h
    constructor
    · intro x A hin
      exact h x A (Or.inl hin)
    · intro x A hin
      exact h x A (Or.inr hin)
  · intro ⟨hΓ, hΔ⟩ x A hin
    cases hin with
    | inl hin => exact hΓ x A hin
    | inr hin => exact hΔ x A hin

lemma Env.lc_perm {n : Nat} {Γ Δ : Env} :
  Γ ~ Δ → (Γ.lc n ↔ Δ.lc n) := by
  intro hPerm
  simp [Env.lc]
  constructor
  · intro h x A hin
    rw [List.Perm.mem_iff hPerm.symm] at hin
    exact h x A hin
  · intro h x A hin
    rw [List.Perm.mem_iff hPerm] at hin
    exact h x A hin

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := List Env
-- instance : Coe Env HyperEnv := ⟨fun Γ => ([Γ] : HyperEnv)⟩

def HyperEnv.names (𝒢 : HyperEnv) : Finset FPName :=
  𝒢.foldr (fun Γ acc => Γ.names ∪ acc) ∅

@[simp] def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  Disjoint 𝒢.names ℋ.names

def HyperEnv.PairwiseDisjoint (𝒢 : HyperEnv) : Prop :=
  List.Pairwise Env.disjoint 𝒢

-- d : Depth shift should be applied
-- c : Correction / how much to shift
def HyperEnv.shiftTypes (d c : Nat) (𝒢 : HyperEnv) : HyperEnv :=
  𝒢.map (fun Γ => Γ.shiftTypes d c)

instance : HasShiftTypes HyperEnv where shift 𝒢 d c := HyperEnv.shiftTypes d c 𝒢

def HyperEnv.substNames (𝒢 : HyperEnv) (T R : FPName) : HyperEnv :=
  𝒢.map (fun Γ => Γ.substNames T R)

instance : HasSubst HyperEnv FPName FPName where subst := HyperEnv.substNames

def HyperEnv.substTypes (𝒢 : HyperEnv) (A : Types) (k : Nat) : HyperEnv :=
  𝒢.map (fun Γ => Γ.substTypes A k)

instance : HasSubst HyperEnv Types Nat where subst := HyperEnv.substTypes

abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ++ ℋ
infixl:55 " |ₕ " => HyperEnv.merge

lemma HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

lemma HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : List.Perm (𝒢 |ₕ ℋ) (ℋ |ₕ 𝒢) := by
  exact List.perm_append_comm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp [HyperEnv.merge]

lemma HyperEnv.merge_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢).Perm (𝒢 |ₕ [Γ]) := by
  symm ; apply List.perm_append_singleton

lemma HyperEnv.merge_swap (𝒢 : HyperEnv) (Γ Δ : Env) :
  List.Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢) := by
  symm ; simpa using List.Perm.swap Γ Δ 𝒢

lemma HyperEnv.subset_names_of_mem {Γ : Env} {G : HyperEnv} (h : Γ ∈ G) :
  Γ.names ⊆ G.names := by
  induction G with
  | nil => contradiction
  | cons Δ 𝒢' ih =>
    simp [HyperEnv.names] at *
    cases h with
    | inl => simp_all
    | inr hΓ =>
      apply Finset.Subset.trans (ih hΓ)
      apply Finset.subset_union_right
