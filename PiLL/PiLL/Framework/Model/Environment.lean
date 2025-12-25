import PiLL.Framework.Model.Process

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env := Finset (PName × Types)

abbrev EmptyEnv : Env := ∅

/- FIXME: eval does not work since non-computable -/
-- noncomputable instance : Repr Env where
--   reprPrec (Γ : Env) _ :=
--     if Γ = ∅ then "∅"
--     else
--       let entries := Γ.toList.map (fun (x, A) => s!"{x} ∶ {reprStr A}")
--       String.intercalate "‚ " entries

-- noncomputable instance : ToString Env where
--   toString e := reprStr e

def Env.mk (x : PName) (A : Types) : Env := {(x, A)}
infixr:86 " ∶ " => Env.mk

-- NOTE: It's a set so linear by definition
-- def Env.linear (Δ : Env) : Prop :=
  -- (Δ.image Prod.fst).card = Δ.card

def Env.names (Δ : Env) : Finset (PName) :=
  (Δ.image Prod.fst)

@[simp] def Env.disjoint (Δ Γ : Env) : Prop :=
  Disjoint Δ.names Γ.names

noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
  -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

notation Δ "⸨" x "⸩ₑ" => Env.lookup Δ x

-- Order independent equality for environments
@[simp] def Env.Eq (Δ Γ : Env) : Prop :=
  ∀ x : (PName), Δ⸨x⸩ₑ = Γ⸨x⸩ₑ

notation Δ " =ₑ " Γ => Env.Eq Δ Γ

-- Eq reflexivity
@[simp] theorem Env.Eq_refl (Δ : Env) : Δ =ₑ Δ :=
  fun _ => rfl

-- Eq symmetry
theorem Env.Eq_symm (Δ Γ : Env) (h : Δ =ₑ Γ) : Γ =ₑ Δ :=
  fun x => (h x).symm

-- Eq transitivity
theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Δ =ₑ Γ) (h₂ : Γ =ₑ Ε) : Δ =ₑ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence Env.Eq :=
⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

infixl:85 "‚ " => Env.merge

-- Merge identity
@[simp] theorem Env.merge_unitR (Δ : Env) : Δ‚ ∅ = Δ := by
  simp [Env.merge]

@[simp] theorem Env.merge_unitL (Δ : Env) : ∅‚ Δ = Δ := by
  simp [Env.merge]


-- Merge commutivity
theorem Env.merge_comm (Δ Γ : Env) : Δ‚ Γ = Γ‚ Δ := by
  simp [Env.merge, Finset.union_comm]

-- Merge associativity
theorem Env.merge_assoc (Δ Γ Ε : Env) : Δ‚ Γ‚ Ε = Δ‚ (Γ‚ Ε) := by
  simp [Env.merge]

lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
  (Γ‚ Δ)‚ Ξ = (Γ‚ Ξ)‚ Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]

lemma Env.merge_move_last_two_left (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ε‚ Δ‚ Ξ := by
  rw [Env.merge_swap_last, Env.merge_swap_last Γ Δ Ε]

lemma Env.merge_move_second_two_right (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ξ‚ Ε‚ Δ := by
  rw [Env.merge_swap_last Γ Δ Ξ, Env.merge_swap_last]

def Env.serverUsable (Γ : Env) : Prop :=
  ∀p, p ∈ Γ → (p.snd).isServerUsable = True

prefix:max "?ₑ" => Env.serverUsable

def Env.freeTypes (Γ : Env) : Finset TVar :=
  Γ.biUnion (fun (_, A) => A.freeTypes)

notation "ft(" Γ ")" => Env.freeTypes Γ

def Env.substName (Γ : Env) (x z : PName) : Env :=
  Γ.image (fun (n, T) => if n = z then (x, T) else (n, T))

instance : HasSubst Env PName PName where subst := Env.substName

def Env.substTypes (Γ : Env) (A : Types) (X : TVar) : Env :=
  Γ.image (fun (n, T) => (n, T.subst A X))

instance : HasSubst Env Types TVar where subst := Env.substTypes

@[simp] lemma Env.serverUsable_substName (Γ : Env) (x z : PName) (h : ?ₑΓ) :
  ?ₑ(Γ{x // z}) := by
  simp only [Env.serverUsable, HasSubst.subst, Env.substName] at *
  simp only [Finset.forall_mem_image, apply_ite] at *
  simp at *
  exact h

@[simp] lemma Env.serverUsable_substTypes (Γ : Env) (A : Types) (X : TVar) (h : ?ₑΓ) :
  ?ₑ(Γ{A // X}) := by
  simp only [Env.serverUsable, HasSubst.subst, Env.substTypes] at *
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨op, hom, heq⟩
  have hou := h op hom
  simp [← heq] at *
  apply Types.isServerUsable_subst
  exact hou

lemma Env.names_substName (Γ : Env) (x z : PName) :
  Γ{x // z}.names = Γ.names.image (fun n => if n = z then x else n) := by
  simp only [Env.names, HasSubst.subst, Env.substName, Finset.image_image]
  apply Finset.image_congr
  intro ⟨n, t⟩ _
  dsimp
  split_ifs <;> rfl

@[simp] lemma Env.substName_eq_self_of_not_mem {Γ : Env} {x z : PName}
  (h : z ∉ Γ.names) : Γ{x // z} = Γ := by
  simp only [HasSubst.subst, Env.substName]
  conv_rhs => rw [← Finset.image_id (s := Γ)]
  apply Finset.image_congr
  intro p hpΓ
  simp_all [Env.names]
  intro a
  subst a
  simp_all

@[simp] lemma Env.names_mk (x : PName) (A : Types) :
  (x ∶ A).names = {x} := by
  simp [Env.names, Env.mk]

@[simp] lemma Env.names_singleton (x : PName) (A : Types) :
  (x ∶ A).names = {x} := by
  simp only [Env.names]
  rfl

@[simp] lemma Env.names_empty : (∅ : Env).names = ∅ := by simp [Env.names]

@[simp] lemma Env.names_distributes (Γ Δ : Env) :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by
    simp only [Env.names, ← Finset.image_union]
    rfl

@[simp] lemma Env.substName_empty (x z : PName) :
  (∅ : Env){x // z} = ∅ := by
  simp only [HasSubst.subst, Env.substName, Finset.image_empty]

@[simp] lemma Env.substName_distributes (Γ Δ : Env) (x z : PName) :
  (Γ‚ Δ){x // z} = Γ{x // z}‚ Δ{x // z} := by
  simp [HasSubst.subst, Env.substName, Env.merge, Finset.image_union]

@[simp] lemma Env.substName_singleton (x y z : PName) (A : Types) :
  (y ∶ A){x // z} = (if y = z then x else y) ∶ A := by
  simp only [HasSubst.subst, Env.substName, Env.mk, Finset.image_singleton]
  split <;> rfl

@[simp] lemma Env.not_mem_substName_intro {Γ : Env} {x y z : PName}
  (hnΓ : y ∉ Γ.names) (hneq : y ≠ x) : y ∉ (Γ{x // z}).names := by
  intro h_contra
  simp [HasSubst.subst, Env.substName, Env.names] at h_contra
  rcases h_contra with ⟨T, pn, h⟩
  split_ifs at h
  · simp_all
  · rcases h with ⟨b, hΓ, heq⟩
    simp_all [Env.names]

@[simp] lemma Env.ft_substName_eq_self (Γ : Env) (x z : PName) :
  ft(Γ{x // z}) = ft(Γ) := by
  simp only [HasSubst.subst, Env.freeTypes, Env.substName]
  rw [Finset.image_biUnion]
  exact Finset.biUnion_congr rfl (by intro p hin ; split <;> rfl)

@[simp] lemma Env.substName_preserves_disjoint {Γ Δ : Env} {x z : PName}
  (hDisj : Γ.disjoint Δ) (hFresh : x ∉ Γ.names ∧ x ∉ Δ.names) :
  Γ{x // z}.disjoint Δ{x // z} := by
  dsimp only [Env.disjoint]
  simp only [Env.names_substName]
  apply Finset.disjoint_image_substName
  · exact hDisj
  · exact hFresh.1
  · exact hFresh.2

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := ∅

instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

/- FIXME: eval does not work since non-computable -/
-- open Lean in
-- noncomputable instance : Repr HyperEnv where
--   reprPrec (𝒢 : HyperEnv) _ :=
--     if 𝒢 = ∅ then "∅"
--     else
--       let entries := 𝒢.toList.map repr
--       Format.joinSep entries " |ₕ "

-- noncomputable instance : ToString HyperEnv where
--   toString g := reprStr g

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

-- FIXME: Relevance?
-- def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
  -- ∀ Δ ∈ 𝒢, Δ.linear ∧                            -- ensure each env is linear
  -- pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
  𝒢.biUnion Env.names

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
  (𝒢.toList.find? (fun Δ => Δ⸨x⸩ₑ ≠ none)) >>= fun Δ  => Δ⸨x⸩ₑ

notation:60 𝒢 "⸨" x "⸩ₕ" => HyperEnv.lookup 𝒢 x

def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar (Linear by definition of Finset)
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  -- 𝒢.linear ∧ ℋ.linear ∧
  -- (𝒢 ∩ ℋ).card = 0 ∧
  -- (𝒢.names ∩ ℋ.names).card = 0
  Disjoint 𝒢.names ℋ.names

-- Order independent equality for hyper-environments
@[simp] def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
  -- (1) 𝒢 and ℋ must define the same names
  -- (2) The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  ∀ x ∈ HyperEnv.names 𝒢, 𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ

notation 𝒢 " =ₕ " ℋ => HyperEnv.Eq 𝒢 ℋ

-- Eq reflexivity
@[simp] theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : 𝒢 =ₕ 𝒢 := by
  simp

-- Eq symmetry
theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : 𝒢 =ₕ ℋ) : ℋ =ₕ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- Eq transitivity
theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : 𝒢 =ₕ ℋ) (h₂ : ℋ =ₕ 𝒦) :
  𝒢 =ₕ 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
    calc
      𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ := h₁_vals x hx
      _          = 𝒦⸨x⸩ₕ := h₂_vals x hxH

instance : Equivalence HyperEnv.Eq :=
⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

infixl:55 " |ₕ " => HyperEnv.merge

-- Merge identity
@[simp] theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

@[simp] theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

-- Merge commutative
theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : 𝒢 |ₕ ℋ = ℋ |ₕ 𝒢 := by
  simp [Finset.union_comm]

-- Merge associativity
theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) : (𝒢 |ₕ ℋ) |ₕ 𝒦 = 𝒢 |ₕ (ℋ |ₕ 𝒦) := by
  simp

def HyperEnv.substName (𝒢 : HyperEnv) (x z : PName) : HyperEnv :=
  𝒢.image (fun Γ => Γ{x // z})

instance : HasSubst HyperEnv PName PName where subst := HyperEnv.substName

def HyperEnv.substTypes (𝒢 : HyperEnv) (A : Types) (X : TVar) : HyperEnv :=
  𝒢.image (fun Γ => Γ.substTypes A X)

instance : HasSubst HyperEnv Types TVar where subst := HyperEnv.substTypes

@[simp] lemma HyperEnv.names_singleton (Γ : Env) :
  ({Γ} : HyperEnv).names = Γ.names := by
  simp [HyperEnv.names, Env.names, Finset.singleton_biUnion]

@[simp] lemma HyperEnv.names_distributes (𝒢 ℋ : HyperEnv) :
  (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  simp only [HyperEnv.names, Finset.biUnion_union]

@[simp] lemma HyperEnv.names_empty : (∅ : HyperEnv).names = ∅ := by simp [HyperEnv.names]

lemma HyperEnv.substName_merge (𝒢 ℋ : HyperEnv) (x z : PName) :
  𝒢{x // z} |ₕ ℋ{x // z} = (𝒢 |ₕ ℋ){x // z} := by
  simp [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]

lemma HyperEnv.names_substName (𝒢 : HyperEnv) (x z : PName) :
  𝒢{x // z}.names = 𝒢.names.image (fun n => if n = z then x else n) := by
  simp only [HyperEnv.names, HasSubst.subst, HyperEnv.substName]
  rw [Finset.biUnion_image]
  rw [Finset.image_biUnion]
  apply Finset.biUnion_congr
  · rfl
  · intro Γ _
    apply Env.names_substName

@[simp] lemma HyperEnv.substName_preserves_disjoint (𝒢 ℋ : HyperEnv) (x z : PName)
  (hDisj : 𝒢.disjoint ℋ) (hFresh : x ∉ 𝒢.names ∧ x ∉ ℋ.names) :
  𝒢{x // z}.disjoint ℋ{x // z} := by
  dsimp only [HyperEnv.disjoint]
  simp only [HyperEnv.names_substName]
  apply Finset.disjoint_image_substName
  · exact hDisj
  · exact hFresh.1
  · exact hFresh.2

lemma HyperEnv.substName_eq_self_of_not_mem (𝒢 : HyperEnv) (x z : PName)
  (h : z ∉ 𝒢.names) : 𝒢{x // z} = 𝒢 := by
  simp only [HasSubst.subst, HyperEnv.substName, Env.substName]
  conv_rhs => rw [← Finset.image_id (s := 𝒢)]
  apply Finset.image_congr
  intro Γ hΓ𝒢
  simp
  apply Env.substName_eq_self_of_not_mem
  simp_all [HyperEnv.names]

@[simp] lemma HyperEnv.substName_empty (x z : PName) :
  (∅ : HyperEnv){x // z} = ∅ := by
  simp only [HasSubst.subst, HyperEnv.substName, Finset.image_empty]

@[simp] lemma HyperEnv.substName_singleton (Γ : Env) (x z : PName) :
  ({Γ} : HyperEnv){x // z} = Γ{x // z} := by
  simp only [HasSubst.subst, HyperEnv.substName, Finset.image_singleton]

@[simp] lemma HyperEnv.substName_distributes (𝒢 ℋ : HyperEnv) (x z : PName) :
  (𝒢 |ₕ ℋ){x // z} = 𝒢{x // z} |ₕ ℋ{x // z} := by
  simp only [HasSubst.subst, HyperEnv.substName, HyperEnv.merge, Finset.image_union]

@[simp] lemma HyperEnv.not_mem_substName_intro {𝒢 : HyperEnv} {x y z : PName}
  (hnΓ : y ∉ 𝒢.names) (hneq : x ≠ y) : y ∉ (𝒢{x // z}).names := by
  intro h_contra
  simp [HasSubst.subst, HyperEnv.substName, HyperEnv.names,
    Env.substName, Env.names] at h_contra
  rcases h_contra with ⟨Γ, h1⟩
  rcases h1 with ⟨hΓ𝒢, T, on, oT, hΓ, heq⟩
  split_ifs at heq with hz
  · simp at heq
    rw [heq.1] at hneq
    contradiction
  · simp_all [HyperEnv.names, Env.names]
