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

abbrev Env := List Elem

instance : HasPerm Env where perm := List.Perm

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

@[simp] lemma Env.substNames_singleton {x y : FPName} {A : Types} :
  ([x ∶ A] : Env){y // x} = [x{y // x} ∶ A] := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]

@[simp] lemma Env.substNames_distributes {Γ : Env} {x y z : FPName} {A : Types} :
  (z ∶ A :: Γ){y // x} = z{y // x} ∶ A :: Γ{y // x} := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]
  split_ifs <;> rfl

@[simp] lemma Env.substNames_merge {Γ Δ : Env} {x y : FPName} :
  (Γ ++ Δ){y // x} =  Γ{y // x} ++ Δ{y // x} := by
  simp [HasSubst.subst, Env.substNames]

@[simp] lemma Env.substNames_nil {x y : FPName} :
  ([] : Env){x // y} = [] := by simp [HasSubst.subst, Env.substNames]

@[simp] lemma Env.mem_pair_fst_in_names_iff {Γ : Env} {x : FPName} :
   x ∈ Γ.names ↔ ∃ A, (x, A) ∈ Γ := by simp_all [Env.names]

@[simp] lemma Env.mem_pair_fst_in_names {Γ : Env} {x : FPName} :
   ∀ A, (x, A) ∈ Γ → x ∈ Γ.names := by
   intro A hin
   cases hin
   case head => simp_all
   case tail hd tl hin =>
    simp_all
    use A
    exact Or.inr hin

@[simp] lemma Env.mem_names_impl_mem_substNames {Γ : Env} {x y : FPName} :
  x ∈ Γ.names → y ∈ Γ{y // x}.names := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.mem_names_impl_mem_substNames' {Γ : Env} {x y : FPName}
  {hF : ∀ A, (y, A) ∉ Γ} :
  y ∈ Γ{y // x}.names → x ∈ Γ.names := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind

@[simp] lemma Env.mem_names_substNames_iff {Γ : Env} {x y z : FPName} :
  z ∈ Γ{y // x}.names ↔ (z = y ∧ x ∈ Γ.names) ∨ (z ∈ Γ.names ∧ z ≠ x) := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind

@[simp] lemma Env.mem_substNames {Γ : Env} {x y : FPName} {A : Types} :
  (x, A) ∈ Γ → (y, A) ∈ Γ{y // x} := by
  simp_all [HasSubst.subst, Env.substNames]
  grind [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.mem_substNames_of_ne {Γ : Env} {x y z : FPName} {A : Types} :
  (z, A) ∈ Γ → z ≠ x → (z, A) ∈ Γ{y // x} := by
  intro hin hneq
  simp [HasSubst.subst, Env.substNames]
  use z
  constructor
  · split_ifs with h
    · constructor
      · apply hin
      · simp_all
    · constructor
      · apply hin
      · rfl

lemma Env.fresh_substNames_aux {Γ : Env} {x y z : FPName}
  (hyz : y = z → y = x) (hyΓ : y ∈ Γ.names → y = x) (hF : z ∉ Γ.names) :
  (z{y // x}) ∉ (Γ{y // x}).names := by
  intro hc
  rw [mem_names_substNames_iff] at hc
  by_cases hzx : z = x <;> (simp [hzx] at hc ; cases hc <;> simp_all)

lemma Env.fresh_substNames {Γ : Env} {x y z : FPName} {A : Types} (hF : z ∉ Γ.names)
  (huniq : ∀ Δ ∈ [z ∶ A :: Γ], ∀ (B : Types), (y, B) ∈ Δ → y = x) :
  z{y // x} ∉ Env.names Γ{y // x} := by
  apply Env.fresh_substNames_aux
  · intro hyz
    exact huniq (z ∶ A :: Γ) (by simp) A (by simp [hyz])
  · intro hyΓ
    obtain ⟨B, hB⟩ := Env.mem_pair_fst_in_names_iff.mp hyΓ
    exact huniq (z ∶ A :: Γ) (by simp) B (by simp [hB])
  · exact hF

@[simp] lemma Env.serverUsable_shiftTypes {d c : Nat} {Γ : Env} :
  ?ₑΓ → ?ₑ(Γ ↑ᵗ d, c) := by
  simp [Env.serverUsable, HasShiftTypes.shift, Env.shiftTypes]
  intro h x A x' A' hMem heq hShift
  have := h x' A' hMem
  apply Types.isServerUsable_shift (d := d) (c := c).mp at this
  simp [HasShiftTypes.shift] at this
  rw [hShift] at this
  exact this

@[simp] lemma Env.shiftTypes_empty {d c : Nat} :
  ([] : Env) ↑ᵗ d, c = ([] : Env) := by
  simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_singleton {d c : Nat} {x : FPName} {A : Types} :
  [x ∶ A] ↑ᵗ d, c = [x ∶ A ↑ᵗ d, c] := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_cons {d k : Nat} {Γ : Env} {x : FPName} {A : Types} :
  (x ∶ A :: Γ) ↑ᵗ d, k = x ∶ A ↑ᵗ d, k :: Γ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_append {d k : Nat} {Γ Δ : Env} :
  (Γ ++ Δ) ↑ᵗ d, k = Γ ↑ᵗ d, k ++ Δ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_preserves_names {d c : Nat} {Γ : Env} :
  (Γ ↑ᵗ d, c).names = Γ.names := by
  simp [HasShiftTypes.shift, Env.shiftTypes, Env.names]
  rfl

@[simp] lemma Env.shiftTypes_preserves_disjoint {d c : Nat} {Γ Δ : Env} :
  Γ.disjoint Δ → (Γ ↑ᵗ d, c).disjoint (Δ ↑ᵗ d, c) := by simp

@[simp] lemma Env.shiftTypes_preserves_perm {d c : Nat} {Γ Δ : Env} :
  (Γ ~ Δ) → (Γ ↑ᵗ d, c ~ Δ ↑ᵗ d, c) := by
  simp [HasShiftTypes.shift]
  apply List.Perm.map

lemma Env.shiftTypes_comm {Γ : Env} {d c : Nat} :
  (Γ.shiftTypes d c).shiftTypes 0 1 = (Γ.shiftTypes 0 1).shiftTypes (d + 1) c := by
  induction Γ <;> grind [Env.shiftTypes, Types.shift_comm_0]

@[simp] lemma Env.substNames_self {Γ : Env} {x : FPName} :
  Γ{x // x} = Γ := by
  induction Γ generalizing x <;> simp_all [HasSubst.subst, Env.substNames]
  case cons hd tl ih =>
    intro h
    obtain ⟨hd1, hd2⟩ := hd
    simp_all

@[simp] lemma Env.not_mem_names_iff {Γ : Env} {x : FPName} :
  x ∉ Γ.names ↔ ∀ A, (x, A) ∉ Γ := by
  simp [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.not_mem_names_cons {Γ : Env} {E : Elem} {x : FPName} :
  x ∉ Env.names (E :: Γ) ↔ x ≠ E.1 ∧ x ∉ Γ.names := by
  simp_all
  constructor
  · intro h
    simp_all
    obtain ⟨E1, E2⟩ := E
    specialize h E2
    simp_all
  · intro A
    obtain ⟨E1, E2⟩ := E
    simp_all

@[simp] lemma Env.substNames_of_not_mem {Γ : Env} {x y : FPName} :
  x ∉ Γ.names → Γ{y // x} = Γ := by
  intro hF
  induction Γ
  case nil => simp
  case cons E Γ ih =>
    cases E
    case mk z A =>
      have : x ≠ z := by
        simp at hF
        specialize hF A
        simp_all
      simp
      constructor
      · apply FPName.subst_self_of_ne (this.symm)
      · exact ih (hF := by simp_all)

lemma Env.substNames_preserves_Types {Γ : Env} {x y : FPName} :
  ∀ z A, (z, A) ∈ Γ → (z{y // x}, A) ∈ Γ{y // x} := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]
  intro z A hMem
  use z, A
  simp_all
  split_ifs <;> rfl

lemma Env.mem_serverUsable_Types {Γ : Env} {x : FPName} {A : Types} :
  ?ₑΓ → (x, A) ∈ Γ → A.isServerUsable := by
  intro hServ hMem
  simp [Env.serverUsable] at hServ
  exact hServ x A hMem

lemma Env.serverUsable_substNames {Γ : Env} {x y : FPName} :
  ?ₑΓ → ?ₑΓ{y // x} := by
  intro hServ
  simp [HasSubst.subst, Env.substNames, Env.serverUsable]
  intros z A w B hMem
  split_ifs <;> intro h <;> (
    simp_all
    exact Env.mem_serverUsable_Types hServ hMem
  )

lemma Env.substNames_preserves_perm {Γ Δ : Env} {x y : FPName} :
  Γ ~ Δ → Γ{y // x} ~ Δ{y // x} := by
  simp_all [HasPerm.perm, HasSubst.subst, Env.substNames]
  grind

@[simp] lemma Env.shiftTypes_substNames_comm {Γ : Env} {x y : FPName} :
  (Γ{y // x})⁺ᵗ = (Γ⁺ᵗ){y // x} := by
  simp_all [HasSubst.subst, Env.substNames, HasShiftTypes.shift, Env.shiftTypes]
  intros ; split_ifs <;> rfl

lemma Env.mem_shiftTypes_iff {Γ : Env} {y : FPName} {T : Types} :
  (y, T) ∈ Γ⁺ᵗ ↔ ∃ A, (y, A) ∈ Γ ∧ T = A⁺ᵗ := by
  induction Γ
  case nil => simp
  case cons hd tl ih =>
    match hd with
    | (x, B) => simp_all ; grind


macro "fresh_substNames_binary_aux"
  z:term ", " C:term ", " Γ:term ", " Δ:term ", " huniq:term: tactic =>
  `(tactic| (
    intro Ξ hin T hMem
    simp at hin; subst hin
    simp at hMem
    rcases hMem with ⟨hyz, rfl⟩ | hin
    · exact $huniq ($z ∶ $C :: $Γ ++ $Δ) (by simp) $C (by simp [hyz])
    · apply $huniq ($z ∶ $C :: $Γ ++ $Δ) (by simp) T
      simp
      right ; left ; exact hin
      simp
  ))

lemma Env.fresh_substNames_binary {Γ Δ : Env} {x y z : FPName} {C : Types}
  (hF : z ∉ Γ.names ∧ z ∉ Δ.names)
  (huniq : ∀ Γ_1 ∈ [z ∶ C :: Γ ++ Δ], ∀ (T : Types), (y, T) ∈ Γ_1 → y = x) :
  z{y // x} ∉ Γ{y // x}.names ∧ z{y // x} ∉ Δ{y // x}.names := by
  cases hF
  case intro hFΓ hFΔ =>
  constructor
  · exact Env.fresh_substNames hFΓ (A := C) (by simp_all ; grind)
  · exact Env.fresh_substNames hFΔ (A := C) (by simp_all ; grind)

@[simp] lemma Env.serverUsable_substTypes {Γ : Env} {A : Types} {k : Nat} (h : ?ₑΓ) :
  (Γ.substTypes A k).serverUsable := by
  induction Γ
  case nil => intro p hp ; contradiction
  case cons hd tl ih =>
    match hd with
    | (x, T) =>
      intro p hp
      have hxT := by apply h (x, T) ; simp
      have htl : ?ₑtl := by intro q hq ; apply h q ; simp [hq]
      simp [Env.substTypes] at hp
      cases hp with
      | inl hphd =>
        rw [hphd] ; simp
        apply Types.isServerUsable_subst hxT
      | inr hptl =>
        apply ih htl
        simp [Env.substTypes]
        exact hptl

@[simp] lemma Env.substTypes_singleton {x : FPName} {A : Types} {k : Nat} :
  ([x ∶ A] : Env){A // k} = [x ∶ A{A // k}] := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_distributes {Γ : Env} {x : FPName} {A B : Types} {k : Nat} :
  (x ∶ B :: Γ){A // k} = x ∶ B{A // k} :: Γ{A // k} := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_merge {Γ Δ : Env} {A : Types} {k : Nat} :
  (Γ ++ Δ){A // k} =  Γ{A // k} ++ Δ{A // k} := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_nil {A : Types} {k : Nat} :
  ([] : Env){A // k} = [] := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_preserves_names {Γ : Env} {A : Types} {k : Nat} :
  Γ{A // k}.names = Γ.names := by
  simp [HasSubst.subst, Env.substTypes, Env.names]
  rfl

@[simp] lemma Env.substTypes_preserves_disjoint {Γ Δ : Env} {A : Types} {k : Nat} :
  Γ.disjoint Δ → Γ{A // k}.disjoint Δ{A // k} := by
  simp [Env.disjoint]

@[simp] lemma Env.substTypes_preserves_perm {Γ Δ : Env} {A : Types} {k : Nat} :
  (Γ ~ Δ) → (Γ{A // k} ~ Δ{A // k}) := by
  simp [HasPerm.perm, HasSubst.subst]
  apply List.Perm.map

-- Γ{A // k}⁺ᵗ = Γ⁺ᵗ{A⁺ᵗ // k + 1}
@[simp] lemma Env.shiftTypes_substTypes_comm {Γ : Env} {A : Types} {k : Nat} :
  (Γ.substTypes A k).shiftTypes 0 1 = (Γ.shiftTypes 0 1).substTypes (A.shift 0 1) (k + 1) := by
  induction Γ <;> simp [Env.substTypes, Env.shiftTypes, Types.shift_0_subst_comm]

lemma Env.perm_disjoint {Γ Δ Ξ : Env} (hP : Γ ~ Δ) :
  Γ.disjoint Ξ ↔ Δ.disjoint Ξ := by
  simp [Env.disjoint]
  rw [← Env.names_eq_of_perm hP]

lemma Env.disjoint_symm {Γ Δ : Env} : Env.disjoint Γ Δ ↔ Env.disjoint Δ Γ := by
  exact disjoint_comm

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := List Env
-- instance : Coe Env HyperEnv := ⟨fun Γ => ([Γ] : HyperEnv)⟩

-- Deep version of List.Perm, where nil, swap and trans mimic List.Perm, but cons
-- allows exchanging the head element with another permutation equivalent element
inductive HyperEnv.Perm : HyperEnv → HyperEnv → Prop where
  | nil : Perm [] []

  | cons {Γ Δ : Env} {𝒢 ℋ : HyperEnv} : (Γ ~ Δ) → Perm 𝒢 ℋ → Perm (Γ :: 𝒢) (Δ :: ℋ)

  | swap (Γ Δ : Env) (𝒢 : HyperEnv) : Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢)

  | trans {𝒢 ℋ 𝒥 : HyperEnv} : Perm 𝒢 ℋ → Perm ℋ 𝒥 → Perm 𝒢 𝒥

instance : HasPerm HyperEnv where perm := HyperEnv.Perm

@[simp] lemma HyperEnv.Perm.refl (𝒢 : HyperEnv) : Perm 𝒢 𝒢 := by
  induction 𝒢 with
  | nil => exact Perm.nil
  | cons Γ 𝒢 ih => exact Perm.cons (List.Perm.refl _) ih

lemma HyperEnv.Perm.rfl {𝒢 : HyperEnv} : 𝒢 ~ 𝒢 := .refl _

lemma HyperEnv.Perm.symm {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) : ℋ ~ 𝒢 := by
  induction hP with
  | nil => exact nil
  | cons hPE hPH ih => exact Perm.cons (hPE.symm) ih
  | swap Γ Δ ℋ => exact Perm.swap ..
  | trans _ _ ih1 ih2 => exact Perm.trans ih2 ih1

lemma HyperEnv.Perm.comm {𝒢 ℋ : HyperEnv} : 𝒢 ~ ℋ ↔ ℋ ~ 𝒢 := ⟨Perm.symm, Perm.symm⟩

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

@[simp] lemma HyperEnv.substNames_singleton {Γ : Env} {x y : FPName} :
  ([Γ] : HyperEnv){y // x} = [Γ{y // x}] := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_distributes {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
  (Γ :: 𝒢){y // x} = Γ{y // x} :: 𝒢{y // x} := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_merge {𝒢 ℋ : HyperEnv} {x y : FPName} :
  (𝒢 |ₕ ℋ){y // x} = 𝒢{y // x} |ₕ ℋ{y // x} := by
  simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_nil {x y : FPName} :
  ([] : HyperEnv){y // x} = [] := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.shiftTypes_empty {d c : Nat} :
  ([] : HyperEnv) ↑ᵗ d, c = ([] : HyperEnv) := by
  simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_singleton {d c : Nat} {Γ : Env} :
  [Γ] ↑ᵗ d, c = [Γ ↑ᵗ d, c] := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_cons {d k : Nat} {𝒢 : HyperEnv} {Γ : Env} :
  (Γ :: 𝒢) ↑ᵗ d, k = Γ ↑ᵗ d, k :: 𝒢 ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes, Env.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_append {d k : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢 ++ ℋ) ↑ᵗ d, k = 𝒢 ↑ᵗ d, k ++ ℋ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.namesTypes_cons {Γ : Env} {𝒢 : HyperEnv} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.shiftTypes_preserves_names {d c : Nat} {𝒢 : HyperEnv} :
  (𝒢 ↑ᵗ d, c).names = 𝒢.names := by
  induction 𝒢 <;> simp_all

@[simp] lemma HyperEnv.shiftTypes_preserves_disjoint {d c : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢.disjoint ℋ) → ((𝒢 ↑ᵗ d, c).disjoint (ℋ ↑ᵗ d, c)) := by simp

@[simp] lemma HyperEnv.shiftTypes_preserves_perm {d c : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢 ~ ℋ) → (𝒢 ↑ᵗ d, c ~ ℋ ↑ᵗ d, c) := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.shiftTypes_preserves_perm hPE) ih
  | swap Γ Δ 𝒢 => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

@[simp] lemma HyperEnv.substNames_self {𝒢 : HyperEnv} {x : FPName} :
  𝒢{x // x} = 𝒢 := by induction 𝒢 generalizing x <;> simp_all

@[simp] lemma HyperEnv.substNames_of_not_mem {𝒢 : HyperEnv} {x : FPName} :
  x ∉ 𝒢.names → (𝒢{x // x} = 𝒢) := by induction 𝒢 <;> simp

lemma HyperEnv.substNames_preserves_perm {𝒢 ℋ : HyperEnv} {x y : FPName} :
  𝒢 ~ ℋ → 𝒢{y // x} ~ ℋ{y // x} := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.substNames_preserves_perm hPE) ih
  | swap => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

lemma HyperEnv.mem_pair_fst_in_names {𝒢 : HyperEnv} {x : FPName} :
   x ∈ 𝒢.names ↔ ∃ A Γ, (x, A) ∈ Γ ∧ Γ ∈ 𝒢 := by
   induction 𝒢
   case nil => simp_all [HyperEnv.names]
   case cons hd tl ih =>
    constructor
    case mp =>
      intro h
      simp at h
      cases h
      case inl hL =>
        cases hL
        case intro T hin =>
          use T, hd
          exact ⟨hin, by simp⟩
      case inr hR =>
        have := ih.mp hR
        simp_all
        obtain ⟨T, Γ, hinΓ, hinℋ⟩ := this
        use T, Γ
        exact ⟨hinΓ, by apply Or.inr ; exact hinℋ⟩
    case mpr =>
      intro h
      obtain ⟨T, Γ, hinΓ, hOr⟩ := h
      cases hOr
      case head =>
        simp_all
        apply Or.inl
        use T
      case tail hMem =>
        simp_all
        apply Or.inr
        use T, Γ
        constructor
        · exact hinΓ
        · apply hMem

lemma HyperEnv.mem_names_substNames {𝒢 : HyperEnv} {x y z : FPName} :
  z ∈ (𝒢{y // x}).names ↔ (z = y ∧ x ∈ 𝒢.names) ∨ (z ∈ 𝒢.names ∧ z ≠ x) := by
  induction 𝒢 <;> simp_all [HasSubst.subst, HyperEnv.substNames]
  case nil => simp [HyperEnv.names]
  case cons hd tl ih =>
    constructor
    case mp => grind [Env.substNames, Env.mem_pair_fst_in_names_iff]
    case mpr =>
      intro h
      cases h with
      | inl h' =>
        cases h'
        case inl.intro heq hin =>
          cases hin with
          | inl hin =>
            cases hin
            case inl.intro T hin =>
              apply Or.inl
              use T
              subst heq
              apply Env.mem_substNames hin
          | inr hin => grind
      | inr h' =>
        cases h'
        case inr.intro h1 hneq =>
          cases h1
          case inl hin =>
            cases hin
            case intro T hin =>
              apply Or.inl
              use T
              exact Env.mem_substNames_of_ne hin hneq (y := y)
          case inr => grind

lemma HyperEnv.substNames_preserves_disjoint {𝒢 ℋ : HyperEnv} {x y : FPName}
  (hD : 𝒢.disjoint ℋ) (huniq : ∀ Γ ∈ 𝒢 |ₕ ℋ, ∀ A, (y, A) ∈ Γ → y = x) :
  𝒢{y // x}.disjoint ℋ{y // x} := by
  simp_all only [HyperEnv.disjoint]
  grind [HyperEnv.mem_names_substNames, Finset.disjoint_left, HyperEnv.mem_pair_fst_in_names]

@[simp] lemma HyperEnv.substTypes_singleton {Γ : Env} {A : Types} {k : Nat} :
  ([Γ] : HyperEnv){A // k} = [Γ{A // k}] := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_distributes {𝒢 : HyperEnv} {Γ : Env} {A : Types} {k : Nat} :
  (Γ :: 𝒢){A // k} = Γ{A // k} :: 𝒢{A // k} := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_merge {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  (𝒢 |ₕ ℋ){A // k} =  𝒢{A // k} |ₕ ℋ{A // k} := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_nil {A : Types} {k : Nat} :
  ([] : HyperEnv){A // k} = [] := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_preserves_names {𝒢 : HyperEnv} {A : Types} {k : Nat} :
  𝒢{A // k}.names = 𝒢.names := by
  induction 𝒢 <;> simp_all

@[simp] lemma HyperEnv.substTypes_preserves_disjoint {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  𝒢.disjoint ℋ → 𝒢{A // k}.disjoint ℋ{A // k} := by simp

@[simp] lemma HyperEnv.substTypes_preserves_perm {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  (𝒢 ~ ℋ) → (𝒢{A // k} ~ ℋ{A // k}) := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.substTypes_preserves_perm hPE) ih
  | swap => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

-- 𝒢{A // k}⁺ᵗ = 𝒢⁺ᵗ{A⁺ᵗ // k + 1}
@[simp] lemma HyperEnv.shiftTypes_subst_comm {𝒢 : HyperEnv} {A : Types} {k : Nat} :
  (𝒢.substTypes A k).shiftTypes 0 1 = (𝒢.shiftTypes 0 1).substTypes (A.shift 0 1) (k + 1) := by
  induction 𝒢 <;>
    simp [HyperEnv.substTypes, HyperEnv.shiftTypes, Env.substTypes,
      Env.shiftTypes, Types.shift_0_subst_comm]

lemma HyperEnv.Perm_mem {𝒢 ℋ : HyperEnv} {Γ : Env} (h : 𝒢 ~ ℋ) (hΓ : Γ ∈ ℋ) :
  ∃ Γ', Γ' ∈ 𝒢 ∧ Γ' ~ Γ := by
  induction h generalizing Γ with

  | nil => contradiction

  | cons hHead _ ih =>
    simp only [List.mem_cons] at hΓ
    rcases hΓ with rfl | hTail
    · simp_all
    · obtain ⟨Γ', hMem, hP⟩ := ih hTail
      use Γ'
      constructor
      · exact List.mem_cons_of_mem _ hMem
      · exact hP

  | swap Γ Δ 𝒢 =>
    simp only [List.mem_cons] at hΓ
    rcases hΓ with rfl | rfl | hTail
    · use Γ
      rw [List.mem_cons]
      constructor
      · apply Or.inr
        rw [List.mem_cons]
        exact Or.inl (rfl)
      · simp [HasPerm.perm]
    · use Γ
      constructor
      · rw [List.mem_cons]
        exact Or.inl (rfl)
      · exact List.Perm.refl Γ
    · use Γ
      constructor
      · rw [List.mem_cons]
        apply Or.inr
        rw [List.mem_cons]
        exact Or.inr (hTail)
      · exact List.Perm.refl Γ

  | trans _ _ ih1 ih2 =>
    obtain ⟨Ξ, hΞ, hPΞ⟩ := ih2 hΓ
    obtain ⟨Ξ', hΞ', hPΞ'⟩ := ih1 hΞ
    use Ξ'
    constructor
    · exact hΞ'
    · exact List.Perm.trans hPΞ' hPΞ

lemma HyperEnv.Perm_pairwise_disjoint {𝒢 ℋ : HyperEnv} :
  (𝒢 ~ ℋ) → (List.Pairwise Env.disjoint 𝒢 ↔ List.Pairwise Env.disjoint ℋ) := by
  intro h
  induction h with
  | nil => simp

  | cons hPE hPH ih =>
    rename_i Γ Δ 𝒢' ℋ'
    constructor
    · intro h
      rw [List.pairwise_cons] at ⊢ h
      obtain ⟨h1, h2⟩ := h
      constructor
      · intros Ξ hΞ
        obtain ⟨Ξ', hMemΞ', hPΞ'⟩ := HyperEnv.Perm_mem hPH hΞ
        have hDΔΞ' := (Env.perm_disjoint hPE).mp (h1 Ξ' hMemΞ')
        exact ((Env.perm_disjoint (Ξ := Δ) hPΞ').mp hDΔΞ'.symm).symm
      · exact ih.mp h2
    · intro h
      rw [List.pairwise_cons] at ⊢ h
      obtain ⟨h1, h2⟩ := h
      constructor
      · intros Ξ hΞ
        obtain ⟨Ξ', hMemΞ', hPΞ'⟩ := HyperEnv.Perm_mem hPH.symm hΞ
        have hDΓΞ' := (Env.perm_disjoint hPE).mpr (h1 Ξ' hMemΞ')
        exact ((Env.perm_disjoint (Ξ := Γ) hPΞ').mp hDΓΞ'.symm).symm
      · apply ih.mpr h2

  | swap =>
    rename_i Γ Δ 𝒢'
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    rw [Env.disjoint_symm]
    tauto

  | trans _ _ ih1 ih2 => exact Iff.trans ih1 ih2
