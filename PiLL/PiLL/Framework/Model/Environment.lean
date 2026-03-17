import PiLL.Framework.Model.Process

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Elem := (FPName × Types)

abbrev Elem.mk (x : FPName) (A : Types) : Elem := (x, A)
infixr:68 " ∶ " => Elem.mk

abbrev Env := List Elem

instance : HasPerm Env where perm := List.Perm

@[simp] lemma Env.Perm.nil :
  ([] : Env) ~ ([] : Env) := by simp [HasPerm.perm]

@[simp, refl] lemma Env.Perm.refl (Γ : Env) : Γ ~ Γ := by
  simp [HasPerm.perm]

lemma Env.Perm.rfl {Γ : Env} : Γ ~ Γ := .refl _

lemma Env.Perm.symm {Γ Δ : Env} (hP : Γ ~ Δ) : Δ ~ Γ := by
  simp [HasPerm.perm] at ⊢ hP ; exact hP.symm

lemma Env.Perm.comm {Γ Δ : Env} : Γ ~ Δ ↔ Δ ~ Γ :=
  ⟨Env.Perm.symm, Env.Perm.symm⟩

lemma Env.Perm.cons {a : Elem} {Γ Δ : Env} : Γ ~ Δ → (a :: Γ) ~ (a :: Δ) := by
  simp [HasPerm.perm]

lemma Env.Perm.swap {a b : Elem} {Γ : Env} : (a :: b :: Γ) ~ (b :: a :: Γ) := by
  simp [HasPerm.perm] ; apply List.Perm.swap

lemma Env.Perm.trans {Γ Δ Ξ : Env} : Γ ~ Δ → Δ ~ Ξ → Γ ~ Ξ := by
  simp [HasPerm.perm] ; intros h1 h2 ; exact List.Perm.trans h1 h2

def Env.names (Γ : Env) : Finset FPName :=
  (Γ.map Prod.fst).toFinset

def Env.Nodup (Γ : Env) : Prop := (Γ.map Prod.fst).Nodup

lemma Env.Nodup_cons {x : FPName} {A : Types} {Γ : Env} :
  Env.Nodup ((x, A) :: Γ) ↔ x ∉ Γ.names ∧ Env.Nodup Γ := by
  simp [Env.Nodup, Env.names]

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

lemma Env.serverUsable_cons_mp {Γ : Env} {x : FPName} {A : Types} :
  A.isServerUsable ∧ ?ₑΓ → ?ₑ(x ∶ A :: Γ) := by
  simp [Env.serverUsable, Types.isServerUsable]

lemma Env.serverUsable_cons_mpr {Γ : Env} {x : FPName} {A : Types} :
  ?ₑ(x ∶ A :: Γ) → A.isServerUsable ∧ ?ₑΓ := by
  simp [Env.serverUsable, Types.isServerUsable]

lemma Env.serverUsable_cons_iff {Γ : Env} {x : FPName} {A : Types} :
  A.isServerUsable ∧ ?ₑΓ ↔ ?ₑ(x ∶ A :: Γ) := by
  constructor
  · exact Env.serverUsable_cons_mp
  · exact Env.serverUsable_cons_mpr

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

@[simp] lemma Env.shiftTypes_substTypes_cancel {Γ : Env} {A : Types} :
  Γ⁺ᵗ{A // 0} = Γ := by
  induction Γ
  case nil => simp
  case cons E Γ ih =>
    cases E with
    | mk x T =>
      simp
      exact ih

lemma Env.perm_disjoint {Γ Δ Ξ : Env} (hP : Γ ~ Δ) :
  Γ.disjoint Ξ ↔ Δ.disjoint Ξ := by
  simp [Env.disjoint]
  rw [← Env.names_eq_of_perm hP]

lemma Env.disjoint_symm {Γ Δ : Env} : Env.disjoint Γ Δ ↔ Env.disjoint Δ Γ := by
  exact disjoint_comm

@[simp] lemma Env.names_nil :
  Env.names [] = ∅ := by simp [Env.names]

@[simp] lemma Env.names_singleton {x : FPName} {A : Types} :
  Env.names [x ∶ A] = {x} := by simp [Env.names]

@[simp] lemma Env.names_distributes {Γ : Env} {x : FPName} {A : Types} :
  Env.names (x ∶ A :: Γ) = {x} ∪ Γ.names := by simp [Env.names]

@[simp] lemma Env.names_merge {Γ Δ : Env} :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by simp [Env.names]

@[simp] lemma Env.Nodup_nil :
  Env.Nodup [] := by simp [Nodup]

@[simp] lemma Env.Nodup_singleton {x : FPName} {A : Types} :
  Env.Nodup [x ∶ A] := by simp [Env.Nodup]
lemma Env.Nodup_perm {Γ Δ : Env} (hP : Γ ~ Δ) :
  Env.Nodup Γ → Env.Nodup Δ := by
  intro h
  have hPNames := List.Perm.map Prod.fst hP
  exact (List.Perm.nodup_iff hPNames).mp h

lemma Env.Perm.nodup_iff {Γ Δ : Env} (h : Γ ~ Δ) :
  Env.Nodup Γ ↔ Env.Nodup Δ := by
  unfold Env.Nodup
  have hPNames := List.Perm.map Prod.fst h
  exact List.Perm.nodup_iff hPNames

@[simp] lemma Env.map_fst_shiftTypes {Γ : Env} :
  List.map Prod.fst Γ⁺ᵗ = List.map Prod.fst Γ := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.Nodup_shiftTypes {Γ : Env} :
  Env.Nodup Γ⁺ᵗ ↔ Env.Nodup Γ := by
  unfold Env.Nodup
  rw [Env.map_fst_shiftTypes]

lemma Env.names_empty_nil {Γ : Env} (h : Γ.names = ∅) :
  Γ = [] := by
  induction Γ
  case nil => simp
  case cons E htl ih => cases E ; simp [Env.names_distributes] at h

lemma Env.extract_exp {Γ : Env} {z : FPName}
  (hz : z ∈ Γ.names) (hServ : ?ₑΓ) (hNodup : Env.Nodup Γ) :
  ∃ A Γ', (Γ ~ z ∶ ??A :: Γ') ∧ (?ₑΓ') ∧ (Env.names Γ' = Γ.names \ {z}) := by
  induction Γ
  case nil => contradiction
  case cons E Γ ih =>
    obtain ⟨x, A⟩ := E

    simp [- Env.mem_pair_fst_in_names_iff] at hz

    have hServΓ : ?ₑΓ := by
      intro p hp
      exact hServ p (List.Mem.tail _ hp)

    have hServA : A.isServerUsable := by
      exact hServ (x, A) (List.Mem.head _)

    cases A <;> try contradiction
    case quest A =>
      rcases hz with (rfl | hzΓ)
      · use A, Γ
        refine ⟨List.Perm.refl _, hServΓ, ?_⟩
        simp ; rw [← Finset.erase_eq, Finset.erase_insert]
        have this := (List.nodup_cons.mp hNodup).1
        simp_all
      · obtain ⟨B, Γ', hP', hServ', hNames'⟩ := ih hzΓ hServΓ ((Env.Nodup_cons.mp hNodup).2)
        use B, (x, ??A) :: Γ'
        constructor
        · apply List.Perm.trans (List.Perm.cons _ hP')
          apply List.Perm.swap
        · constructor
          · rw [Env.serverUsable]
            intro p hp
            simp at hp
            cases hp
            case inl h => subst h ; simp ; exact hServA
            case inr h =>
              cases p
              case mk x T =>
                exact Env.mem_serverUsable_Types hServ' h
          · simp [Env.names_distributes]
            rw [hNames']
            simp_all

            have h1 : x ∉ names Γ := by
              have := (List.nodup_cons.mp hNodup).1
              simp at this
              exact Env.not_mem_names_iff.mpr this

            have h2 : z ∈ names Γ := by
              obtain ⟨T, hT⟩ := hzΓ
              simp
              exact ⟨T, hT⟩

            have hneq : z ≠ x := by
              intro rfl
              exact h1 h2

            ext a
            simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
            grind

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

-- inter-component uniqueness
@[simp] def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  Disjoint 𝒢.names ℋ.names

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

-- FIXME: Adapt to use current Deep perm
-- lemma HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : (𝒢 |ₕ ℋ) ~ (ℋ |ₕ 𝒢) := by sorry

-- lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  -- simp [HyperEnv.merge]

-- lemma HyperEnv.merge_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
--   (Γ :: 𝒢).Perm (𝒢 |ₕ [Γ]) := by
--   symm ; apply List.perm_append_singleton

-- lemma HyperEnv.merge_swap (𝒢 : HyperEnv) (Γ Δ : Env) :
--   List.Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢) := by
--   symm ; simpa using List.Perm.swap Γ Δ 𝒢

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

@[simp] lemma HyperEnv.names_cons {Γ : Env} {𝒢 : HyperEnv} :
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

lemma HyperEnv.Perm_PairwiseDisjoint_iff {𝒢 ℋ : HyperEnv} :
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

@[simp] lemma HyperEnv.names_nil :
  HyperEnv.names [] = ∅ := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_singleton (Γ : Env) :
  HyperEnv.names [Γ] = Γ.names := by
  simp [HyperEnv.names, Env.names, List.foldr]

@[simp] lemma HyperEnv.names_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names, Env.names]

@[simp] lemma HyperEnv.names_merge (𝒢 ℋ : HyperEnv) :
  (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  induction 𝒢
  case nil => simp [HyperEnv.names]
  case cons _ _ ih => simp ; rw [ih]

lemma HyperEnv.names_eq_of_perm {𝒢 ℋ : HyperEnv} (h : 𝒢 ~ ℋ) :
  𝒢.names = ℋ.names := by
  induction h with
  | nil => simp
  | cons hPE _ ih => simp ; rw [Env.names_eq_of_perm hPE, ih]
  | swap Γ Δ => simp ; rw [← Finset.union_assoc, Finset.union_comm Γ.names _, Finset.union_assoc]
  | trans _ _ ih1 ih2 => apply Eq.trans ih1 ih2

@[simp, refl] lemma HyperEnv.Perm_refl {𝒢 : HyperEnv} :
  𝒢 ~ 𝒢 := by simp [HasPerm.perm]

@[simp] lemma HyperEnv.Nodup_nil :
  HyperEnv.Nodup [] := by simp [HyperEnv.Nodup]

@[simp] lemma HyperEnv.Nodup_singleton_from_env {Γ : Env} (h : Env.Nodup Γ) :
  HyperEnv.Nodup [Γ] := by simp [HyperEnv.Nodup, h]

@[simp] lemma HyperEnv.Nodup_singleton {Γ : Env} :
  HyperEnv.Nodup [Γ] → Env.Nodup Γ := by simp [HyperEnv.Nodup]

lemma HyperEnv.Nodup_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.Nodup (Γ :: 𝒢) ↔ HyperEnv.Nodup [Γ] ∧ HyperEnv.Nodup  𝒢 := by
  simp [HyperEnv.Nodup]

@[simp] lemma HyperEnv.Nodup_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).Nodup ↔ (𝒢.Nodup ∧ ℋ.Nodup) := by
  simp [HyperEnv.merge, HyperEnv.Nodup, Env.Nodup]
  constructor
  · intro h
    constructor
    · intro Γ hin ; exact h Γ (Or.inl hin)
    · intro Γ hin ; exact h Γ (Or.inr hin)
  · intro h1 Γ hin
    cases hin with
    | inl hin => exact h1.1 Γ hin
    | inr hin => exact h1.2 Γ hin

@[simp] lemma HyperEnv.Nodup_cons_iff {Γ : Env} {x : FPName} {A : Types} (hF : x ∉ Γ.names) :
  HyperEnv.Nodup [x ∶ A :: Γ] ↔ (HyperEnv.Nodup [[x ∶ A]] ∧ HyperEnv.Nodup [Γ]) := by
  simp_all [HyperEnv.Nodup, Env.Nodup_cons]

@[simp] lemma HyperEnv.Nodup_cons {Γ : Env} {x : FPName} {A : Types} :
  HyperEnv.Nodup [x ∶ A :: Γ] → (HyperEnv.Nodup [[x ∶ A]] ∧ HyperEnv.Nodup [Γ]) := by
  simp_all [HyperEnv.Nodup, Env.Nodup_cons]

lemma HyperEnv.Nodup_cons_perm_iff {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.Nodup (Γ :: 𝒢) ↔ HyperEnv.Nodup (Δ :: 𝒢) := by
  constructor
  · intros h E hE
    simp only [List.mem_cons] at hE
    rcases hE with rfl | h_in_G
    · have hNodupΓ : Env.Nodup Γ := by
        apply h
        simp
      exact (Env.Perm.nodup_iff hP).mp hNodupΓ
    · apply h
      simp [h_in_G]
  · intros h E hE
    simp only [List.mem_cons] at hE
    rcases hE with rfl | h_in_G
    · have hNodupΔ : Env.Nodup Δ := by
        apply h
        simp
      exact (Env.Perm.nodup_iff hP).mpr hNodupΔ
    · apply h
      simp [h_in_G]

lemma HyperEnv.Nodup_perm {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  HyperEnv.Nodup 𝒢 → HyperEnv.Nodup ℋ := by
  intro h
  simp_all [Nodup]
  intro E hE
  obtain ⟨Γ, hin, hPE⟩ := (HyperEnv.Perm_mem hP hE)
  exact Env.Nodup_perm hPE (h Γ hin)

lemma HyperEnv.Nodup_perm_iff {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  HyperEnv.Nodup 𝒢 ↔ HyperEnv.Nodup ℋ := by
  constructor
  · intro h ; exact HyperEnv.Nodup_perm hP h
  · intro h ; exact HyperEnv.Nodup_perm hP.symm h

@[simp] lemma HyperEnv.PairwiseDisjoint_nil :
  HyperEnv.PairwiseDisjoint [] := by simp [HyperEnv.PairwiseDisjoint]

@[simp] lemma HyperEnv.PairwiseDisjoint_singleton {Γ : Env} :
  HyperEnv.PairwiseDisjoint [Γ] := by simp [HyperEnv.PairwiseDisjoint]

@[simp] lemma HyperEnv.PairwiseDisjoint_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).PairwiseDisjoint ↔ (𝒢.PairwiseDisjoint ∧ ℋ.PairwiseDisjoint
    ∧ ∀ a ∈ 𝒢, ∀ b ∈ ℋ, Disjoint a.names b.names) := by
  simp [HyperEnv.merge, HyperEnv.PairwiseDisjoint]
  constructor
  · intro h
    simp [List.pairwise_append] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  · intro h
    rw [List.pairwise_append]
    exact ⟨h.1, h.2.1, h.2.2⟩

@[simp] lemma HyperEnv.PairwiseDisjoint_cons {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) → (HyperEnv.PairwiseDisjoint [Γ] ∧
  HyperEnv.PairwiseDisjoint 𝒢) := by
  simp [HyperEnv.PairwiseDisjoint]

lemma HyperEnv.PairwiseDisjoint_cons_perm {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) → HyperEnv.PairwiseDisjoint (Δ :: 𝒢) := by
  intro h
  simp [HyperEnv.PairwiseDisjoint] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro a ha
    have hDΓ := h1 a ha
    have hPNames := List.Perm.map Prod.fst hP
    have hNamesEq : Γ.names = Δ.names := by
      ext x
      simp [Env.names]
      constructor
      · intro h
        obtain ⟨A, hinΓ⟩ := h
        use A
        exact (List.Perm.mem_iff (a := (x, A)) hP).mp hinΓ
      · intro h
        obtain ⟨A, hinΔ⟩ := h
        use A
        exact (List.Perm.mem_iff (a := (x, A)) hP.symm).mp hinΔ
    rw [← hNamesEq]
    exact hDΓ
  · exact h2

lemma HyperEnv.PairwiseDisjoint_cons_perm_iff {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) ↔ HyperEnv.PairwiseDisjoint (Δ :: 𝒢) := by
  constructor
  · intro h ; exact HyperEnv.PairwiseDisjoint_cons_perm hP h
  · intro h ; exact HyperEnv.PairwiseDisjoint_cons_perm hP.symm h

lemma Env.disjoint_of_perm {Γ Δ Γ' Δ' : Env} (hP1 : Γ ~ Γ') (hP2 : Δ ~ Δ')
  (hDisj : Env.disjoint Γ Δ) : Env.disjoint Γ' Δ' := by
  simp only [Env.disjoint] at *
  have h_names1 : Γ.names = Γ'.names := by
    ext x ; simp [Env.names]
    constructor
    · intro h
      obtain ⟨A, hinΓ⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP1).mp hinΓ
    · intro h
      obtain ⟨A, hinΓ'⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP1.symm).mp hinΓ'
  have h_names2 : Δ.names = Δ'.names := by
    ext x ; simp [Env.names]
    constructor
    · intro h
      obtain ⟨A, hinΔ⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP2).mp hinΔ
    · intro h
      obtain ⟨A, hinΔ'⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP2.symm).mp hinΔ'
  rw [← h_names1, ← h_names2]
  exact hDisj

lemma HyperEnv.mem_of_disjoint {𝒢 ℋ : HyperEnv} (hD : 𝒢.disjoint ℋ) :
  ∀ Γ ∈ 𝒢, ∀ Δ ∈ ℋ, Γ.disjoint Δ := by
  intro Γ hΓ Δ hΔ
  apply Disjoint.mono _ _ hD
  · exact HyperEnv.subset_names_of_mem hΓ
  · exact HyperEnv.subset_names_of_mem hΔ
