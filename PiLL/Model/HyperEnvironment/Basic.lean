import PiLL.Model.Environment.Basic

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

@[simp, refl] lemma HyperEnv.Perm.refl (𝒢 : HyperEnv) : Perm 𝒢 𝒢 := by
  induction 𝒢 with
  | nil => exact Perm.nil
  | cons Γ 𝒢 ih => exact Perm.cons (List.Perm.refl _) ih

lemma HyperEnv.Perm.rfl {𝒢 : HyperEnv} : 𝒢 ~ 𝒢 := .refl _

@[symm] lemma HyperEnv.Perm.symm {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) : ℋ ~ 𝒢 := by
  induction hP with
  | nil => exact nil
  | cons hPE hPH ih => exact Perm.cons (hPE.symm) ih
  | swap Γ Δ ℋ => exact Perm.swap ..
  | trans _ _ ih1 ih2 => exact Perm.trans ih2 ih1

lemma HyperEnv.Perm.comm {𝒢 ℋ : HyperEnv} : 𝒢 ~ ℋ ↔ ℋ ~ 𝒢 := ⟨Perm.symm, Perm.symm⟩

def HyperEnv.names (𝒢 : HyperEnv) : Finset FPName :=
  𝒢.foldr (fun Γ acc => Γ.names ∪ acc) ∅

-- intra-component uniqueness
def HyperEnv.Nodup (𝒢 : HyperEnv) : Prop :=
  ∀ Γ ∈ 𝒢, Env.Nodup Γ

@[simp] def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  Disjoint 𝒢.names ℋ.names

-- inter-component uniqueness
def HyperEnv.PairwiseDisjoint (𝒢 : HyperEnv) : Prop :=
  List.Pairwise Env.disjoint 𝒢

-- d : Depth shift should be applied
-- c : Correction / how much to shift
def HyperEnv.shiftTypes (d c : Nat) (𝒢 : HyperEnv) : HyperEnv :=
  𝒢.map (fun Γ => Γ.shiftTypes d c)
instance : HasShiftTypes HyperEnv where shift 𝒢 d c := HyperEnv.shiftTypes d c 𝒢

def HyperEnv.substNames (𝒢 : HyperEnv) (R T : FPName) : HyperEnv :=
  𝒢.map (fun Γ => Γ.substNames R T)
instance : HasSubst HyperEnv FPName FPName where subst := HyperEnv.substNames

def HyperEnv.substTypes (𝒢 : HyperEnv) (A : Types) (k : Nat) : HyperEnv :=
  𝒢.map (fun Γ => Γ.substTypes A k)
instance : HasSubst HyperEnv Types Nat where subst := HyperEnv.substTypes

abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ++ ℋ
infixl:55 " |ₕ " => HyperEnv.merge

lemma HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp
