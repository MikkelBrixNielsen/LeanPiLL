import PiLL.Model.Process

-- Has been added s.t. the below set_option does not trigger an unscoped linter warning
set_option linter.style.setOption false
-- Has been added to disable some new linters as to not use too much time conforming to these
-- as they primarly regard lean not being happy with the use of unbound simp statements and
-- want them replaced with simp only variants.
set_option linter.flexible false
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
infixl:69 "‚ " => Env.merge

lemma Env.merge_unitL (Γ : Env) : ∅‚ Γ = Γ := by simp

lemma Env.merge_unitR (Γ : Env) : Γ‚ ∅ = Γ := by simp

lemma Env.cons_nil {e : Elem} : e :: ∅ = [e] := by simp

lemma Env.cons_empty {e : Elem} : e :: [] = [e] := by simp

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

@[simp] lemma Env.substNames_empty {x y : FPName} : (∅ : Env){x // y} = ∅ := by
  simp

@[simp] lemma Env.mem_pair_fst_in_names_iff {Γ : Env} {x : FPName} :
   x ∈ Γ.names ↔ ∃ A, (x, A) ∈ Γ := by simp_all [Env.names]

@[simp] lemma Env.mem_pair_fst_in_names {Γ : Env} {x : FPName} :
   ∀ A, (x, A) ∈ Γ → x ∈ Γ.names := by
   intro A hin
   cases hin
   case head => simp_all [Env.mem_pair_fst_in_names_iff]
   case tail hd tl hin =>
    simp_all [Env.mem_pair_fst_in_names_iff]
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
        simp [Env.mem_pair_fst_in_names_iff] at hF
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
    · exact $huniq:term ($z ∶ $C :: $Γ ++ $Δ) (by simp) $C (by simp [hyz])
    · apply $huniq:term ($z ∶ $C :: $Γ ++ $Δ) (by simp) T
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
    simp [- mem_pair_fst_in_names_iff] at hz
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
        simp_all [Env.mem_pair_fst_in_names_iff]
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
            have hneq : z ≠ x := by
              intro rfl
              exact h1 (by simp [hzΓ])
            ext a
            simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
            grind

@[simp] lemma Env.serverUsable_nil :
  ?ₑ[] := by simp [Env.serverUsable]

@[simp] lemma Env.swap_two {x y : FPName} {A B : Types} :
  [x ∶ A, y ∶ B] ~ [y ∶ B, x ∶ A] := by
  exact List.Perm.swap ..
lemma Env.not_mem_names_substNames {Γ : Env} {x y z : FPName} (hzy : z ≠ y) (hz : z ∉ Γ.names) :
  z ∉ Γ{y // x}.names := by
  induction Γ
  case nil => simp
  case cons E Δ ih =>
    obtain ⟨w, T⟩ := E
    simp at ⊢ hz
    constructor
    · simp [HasSubst.subst, FPName.subst]
      split_ifs
      case pos => exact hzy
      case neg => exact hz.1
    · simp_all

@[simp] lemma Env.lc_nil {n : Nat} :
  Env.lc n ([] : Env) := by simp [Env.lc]

lemma Env.substNames_preserves_lc {Γ : Env} {x y : FPName} {n : Nat} (hlc : Env.lc n Γ) :
  Env.lc n Γ{y // x} := by
  induction Γ
  case nil => simp
  case cons E Δ ih =>
    obtain ⟨w, T⟩ := E
    simp [Env.lc_cons] at ⊢ hlc
    constructor
    · exact hlc.1
    · apply ih
      exact hlc.2

lemma Env.serverUsable_perm_mp {Γ Δ : Env} :
  Γ ~ Δ → (?ₑΓ → ?ₑΔ) := by
  intro hP hServ A B
  simp [Env.serverUsable] at hServ
  have hAΓ : A ∈ Γ := (hP.mem_iff).mpr B
  exact hServ A.1 A.2 hAΓ

lemma Env.serverUsable_perm_iff {Γ Δ : Env} :
  Γ ~ Δ → (?ₑΓ ↔ ?ₑΔ) := by
  intro hP
  constructor
  · exact Env.serverUsable_perm_mp hP
  · exact Env.serverUsable_perm_mp hP.symm

lemma Env.serverUsable_merge_mp {Γ Δ : Env} :
  ?ₑ(Γ ++ Δ) → (?ₑΓ ∧ ?ₑΔ) := by
  simp [Env.serverUsable]
  intro h
  constructor
  · intro a b hΓ
    exact h a b (Or.inl hΓ)
  · intro a b hΔ
    exact h a b (Or.inr hΔ)

lemma Env.serverUsable_merge_mpr {Γ Δ : Env} :
  (?ₑΓ ∧ ?ₑΔ) → ?ₑ(Γ ++ Δ) := by
  simp [Env.serverUsable]
  intro hΓ hΔ a b h
  cases h
  case inl h => exact hΓ a b h
  case inr h => exact hΔ a b h

lemma Env.serverUsable_merge_iff {Γ Δ : Env} :
  ?ₑ(Γ ++ Δ) ↔ (?ₑΓ ∧ ?ₑΔ) := by
  constructor
  · exact Env.serverUsable_merge_mp
  · exact Env.serverUsable_merge_mpr

lemma Env.Nodup_merge_iff {Γ Δ : Env} :
  (Γ ++ Δ).Nodup ↔ (Γ.Nodup ∧ Δ.Nodup ∧ Γ.disjoint Δ) := by
  simp [Env.Nodup]
  constructor
  · intro h
    have h' := (List.nodup_append.mp h)
    split_ands
    · exact h'.1
    · exact h'.2.1
    · simp [Disjoint]
      intro x hxΓ hxΔ
      ext a
      constructor
      · intro ha
        rcases h' with ⟨_, _, hdis⟩
        have hΓ := hxΓ ha
        have hΔ := hxΔ ha
        have : a ≠ a := hdis a (by simpa using hΓ) a (by simpa using hΔ)
        exact (this rfl).elim
      · intro h; cases h
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    have := (List.nodup_append.mpr ⟨h1, h2, ?_⟩)
    · exact this
    · simp [Disjoint] at h3
      intro a ha b hb hEq
      have hsubsetΓ : ({a} : Finset FPName) ⊆ Γ.names := by
        intro x hx
        simp at hx
        subst hx
        simpa using ha
      have hsubsetΔ : ({a} : Finset FPName) ⊆ Δ.names := by
        intro x hx
        simp at hx
        subst hx
        simpa [hEq] using hb
      have hEmpty := h3 hsubsetΓ hsubsetΔ
      simp at hEmpty

lemma Env.mem_unique {Γ : Env} {x : FPName} {A B : Types}
  (hNodup : Γ.Nodup) (hA : (x, A) ∈ Γ) (hB : (x, B) ∈ Γ) : A = B := by
  induction Γ
  case nil => contradiction
  case cons hd tl ih =>
    obtain ⟨w, T⟩ := hd
    simp_all
    rw [Env.Nodup_cons] at hNodup
    grind [mem_pair_fst_in_names_iff]

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

@[simp] lemma Env.names_substNames_image_free {Γ : Env} {y x : FPName} :
  (Γ.names.image Channel.free){y // x} = (Γ{y // x}).names.image Channel.free := by
  ext u
  simp only [HasSubst.subst, Finset.subst, Finset.image_image, Env.names, Env.substNames,
    Finset.mem_image, List.mem_toFinset, List.mem_map, Prod.exists, beq_iff_eq]
  constructor
  · rintro ⟨c, ⟨z, B, hin, rfl⟩, rfl⟩
    simp only [↓existsAndEq, and_true, Channel.subst, beq_iff_eq,
      Function.comp_apply, exists_and_right]
    split_ifs with heq
    · subst heq
      use y
      constructor
      · use B, z, B, hin
        simp only [if_true]
      · rfl
    · use z
      constructor
      · use B, z, B, hin
        simp only [heq, if_false]
      · rfl
  · rintro ⟨_, ⟨w, B, ⟨z, B', hin, heq⟩, rfl⟩, rfl⟩
    split_ifs at heq with heq'
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      use z
      constructor
      · use z, B', hin
      · simp only [Channel.subst, beq_iff_eq, heq', Function.comp_apply, ↓reduceIte]
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      use z
      constructor
      · use z, B', hin
      · simp [Channel.subst, heq']

lemma Env.disjoint_cons_iff {Γ Δ : Env} {x y : FPName} {A : Types} :
  Disjoint (Env.names (x ∶ A :: Γ)) (Env.names (y ∶ Aᗮᗮ :: Δ)) ↔
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

lemma HyperEnv.subset_names_of_mem {Γ : Env} {G : HyperEnv} (h : Γ ∈ G) :
  Γ.names ⊆ G.names := by
  induction G with
  | nil => contradiction
  | cons Δ 𝒢' ih =>
    simp only [names, List.mem_cons, List.foldr_cons] at *
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

@[simp] lemma HyperEnv.substNames_of_not_mem {𝒢 : HyperEnv} {x y : FPName} :
  x ∉ 𝒢.names → (𝒢{y // x} = 𝒢) := by
  induction 𝒢
  case nil => simp only [substNames_nil, implies_true]
  case cons E HE ih =>
    simp only [names_cons, Finset.mem_union, not_or, substNames_distributes,
      List.cons.injEq, and_imp] at ⊢ ih
    intros hxE hxHE
    constructor
    · exact Env.substNames_of_not_mem hxE
    · exact ih hxHE

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
      simp [Env.mem_pair_fst_in_names_iff] at h
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
        simp_all [Env.mem_pair_fst_in_names_iff]
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
  induction 𝒢 <;> simp_all [Env.mem_pair_fst_in_names_iff, HasSubst.subst, HyperEnv.substNames]
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

@[simp] lemma HyperEnv.Nodup_singleton {Γ : Env} :
  HyperEnv.Nodup [Γ] = Env.Nodup Γ := by simp [HyperEnv.Nodup]

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

lemma HyperEnv.mem_of_disjoint {𝒢 ℋ : HyperEnv} (hD : 𝒢.disjoint ℋ) :
  ∀ Γ ∈ 𝒢, ∀ Δ ∈ ℋ, Γ.disjoint Δ := by
  intro Γ hΓ Δ hΔ
  apply Disjoint.mono _ _ hD
  · exact HyperEnv.subset_names_of_mem hΓ
  · exact HyperEnv.subset_names_of_mem hΔ

@[simp] lemma HyperEnv.swap_two_inner {x y : FPName} {A B : Types} :
  [[x ∶ A, y ∶ B]] ~ [[y ∶ B, x ∶ A]] := by
  exact HyperEnv.Perm.cons Env.swap_two HyperEnv.Perm.nil

@[simp] lemma HyperEnv.disjoint_split {𝒢 ℋ : HyperEnv} (hD : (𝒢 |ₕ ℋ).PairwiseDisjoint) :
  𝒢.disjoint ℋ := by
  rw [HyperEnv.disjoint, Finset.disjoint_left]
  rw [HyperEnv.PairwiseDisjoint, HyperEnv.merge, List.pairwise_append] at hD
  intro n hin𝒢 hinℋ
  rw [HyperEnv.mem_pair_fst_in_names] at hin𝒢 hinℋ
  obtain ⟨T1, Γ, hinΓ, hΓ𝒢⟩ := hin𝒢
  obtain ⟨T2, Δ, hinΔ, hΔℋ⟩ := hinℋ
  obtain ⟨h1, h2, h3⟩ := hD
  have := h3 Γ hΓ𝒢 Δ hΔℋ
  simp [Env.disjoint] at this
  have hnΓ := Env.mem_pair_fst_in_names T1 hinΓ
  have hnΔ := Env.mem_pair_fst_in_names T2 hinΔ
  rw [Finset.disjoint_left] at this
  exact this hnΓ hnΔ

lemma HyperEnv.merge_nilL (𝒢 : HyperEnv) : [] |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_nilR (𝒢 : HyperEnv) : 𝒢 |ₕ [] = 𝒢 := by simp

lemma HyperEnv.Perm.merge_right {𝒢 ℋ : HyperEnv} (p : 𝒢 ~ ℋ) : ∀ 𝒥, 𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 := by
  induction p
  case nil => simp
  case cons hPE hPH ih => intro 𝒥 ; exact HyperEnv.Perm.cons hPE (ih 𝒥)
  case swap => intro 𝒥 ; exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => intro 𝒥 ; exact HyperEnv.Perm.trans (ih1 𝒥) (ih2 𝒥)

theorem HyperEnv.Perm.merge_left {𝒢 ℋ : HyperEnv} : 𝒢 ~ ℋ → ∀ 𝒥, 𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ := by
  intro h 𝒥
  induction 𝒥
  case nil => exact h
  case cons Γ ℐ ih => apply HyperEnv.Perm.cons (.refl _) ih

theorem HyperEnv.Perm.merge {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
  𝒢 |ₕ ℋ ~ 𝒢' |ₕ ℋ' := (p₁.merge_right ℋ).trans (p₂.merge_left _)

@[simp] lemma HyperEnv.Perm_middle {Γ : Env} : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ Γ :: ℋ ~ Γ :: (𝒢 |ₕ ℋ)
  | [], _ => .refl _
  | Δ :: _, _ =>
    (HyperEnv.Perm.cons (.refl _) Perm_middle).trans (HyperEnv.Perm.swap Δ Γ _)

lemma HyperEnv.Perm.merge_exchange_right {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (𝒢 |ₕ ℋ ~ 𝒢 |ₕ 𝒥) := by
  intro h
  induction 𝒢
  case nil => simp ; exact h
  case cons ih => apply HyperEnv.Perm.cons (by rfl) ih

lemma HyperEnv.Perm.merge_exchange_left {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (ℋ |ₕ 𝒢 ~ 𝒥 |ₕ 𝒢 ) := by
  intro h
  induction h
  case nil => simp
  case cons hPE hPH ih => exact HyperEnv.Perm.cons hPE ih
  case swap => exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

lemma HyperEnv.Perm.merge_comm : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ ℋ ~ ℋ |ₕ 𝒢
  | [], _ => by simp
  | _ :: _, _ => (HyperEnv.Perm.merge_comm.cons (.refl _)).trans HyperEnv.Perm_middle.symm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp only [List.append_assoc]

lemma HyperEnv.Perm.merge_assoc (𝒢 ℋ ℐ : HyperEnv) :
  (𝒢 |ₕ (ℋ |ₕ ℐ)) ~ (ℋ |ₕ (𝒢 |ₕ ℐ)) := by
  repeat rw [← HyperEnv.merge_assoc]
  apply HyperEnv.Perm.merge_right HyperEnv.Perm.merge_comm

lemma HyperEnv.Perm.merge_cons {Γ : Env} {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
    𝒢 |ₕ Γ :: ℋ ~ 𝒢' |ₕ Γ :: ℋ' := p₁.merge (p₂.cons (.refl _))

@[simp] lemma HyperEnv.Perm_merge_singleton (Γ : Env) (𝒢 : HyperEnv) : 𝒢 |ₕ [Γ] ~ Γ :: 𝒢 :=
  HyperEnv.Perm_middle.trans <| by rw [HyperEnv.merge_nilR]

lemma HyperEnv.Perm_merge_comm : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ ℋ ~ ℋ |ₕ 𝒢
  | [], _ => by simp
  | _ :: _, _ => (HyperEnv.Perm_merge_comm.cons (.refl _)).trans HyperEnv.Perm_middle.symm

theorem HyperEnv.Perm_merge_comm_assoc (𝒢 ℋ 𝒥 : HyperEnv) :
    (𝒢 |ₕ (ℋ |ₕ 𝒥)) ~ (ℋ |ₕ (𝒢 |ₕ 𝒥)) := by
  simpa only [List.append_assoc] using HyperEnv.Perm_merge_comm.merge_right _

lemma HyperEnv.cons_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢) ~ (𝒢 |ₕ [Γ]) := by
  symm ; apply HyperEnv.Perm_merge_singleton

lemma HyperEnv.cons_append {𝒢 : HyperEnv} {Γ : Env} :
  Γ :: 𝒢 = [Γ] |ₕ 𝒢 := by simp

inductive HyperEnv.Delete (Γ : Env) : HyperEnv → HyperEnv → Prop where
  | head {𝒢 : HyperEnv} {Δ : Env} :
      (Γ ~ Δ) → Delete Γ (Δ :: 𝒢) 𝒢
  | tail {Δ : Env} {𝒢 𝒢' : HyperEnv} :
      Delete Γ 𝒢 𝒢' → Delete Γ (Δ :: 𝒢) (Δ :: 𝒢')

-- Removing Γ from Γ :: 𝒢 => 𝒢 then adding Γ again => Γ :: 𝒢
lemma HyperEnv.Delete_restore {Γ : Env} {𝒢 𝒢' : HyperEnv} (h : Delete Γ 𝒢 𝒢') :
  Γ :: 𝒢' ~ 𝒢 := by
  induction h
  case head Δ hEnv =>
    exact HyperEnv.Perm.cons hEnv (.refl _)
  case tail Δ hD ih =>
    apply HyperEnv.Perm.trans (HyperEnv.Perm.swap ..)
    exact HyperEnv.Perm.cons (List.Perm.refl _) ih

lemma HyperEnv.Perm_Delete {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  ∀ {Γ 𝒢'}, Delete Γ 𝒢 𝒢' → ∃ ℋ', Delete Γ ℋ ℋ' ∧ 𝒢' ~ ℋ' := by
  induction hP
  case nil => intros _ 𝒢 _ ; use 𝒢
  case cons Γ Δ 𝒢 ℋ hPE hPH ih =>
    intros Ξ 𝒥 hDel
    cases hDel
    case head hP' =>
      exact ⟨ℋ, HyperEnv.Delete.head (List.Perm.trans hP' hPE), hPH⟩
    case tail 𝒥 hDel =>
      obtain ⟨ℋ', hDelℋ', hPℋ'⟩ := ih hDel
      exact ⟨Δ :: ℋ', HyperEnv.Delete.tail hDelℋ', HyperEnv.Perm.cons hPE hPℋ'⟩
  case swap Γ Δ 𝒢 =>
    intro Ξ 𝒢' hDel
    cases hDel
    case head hEnv =>
      exact ⟨Δ :: 𝒢, HyperEnv.Delete.tail (HyperEnv.Delete.head hEnv), .refl _⟩
    case tail hD_tail =>
      cases hD_tail
      case head hPE =>
        use Γ :: 𝒢
        exact ⟨HyperEnv.Delete.head hPE, .refl _⟩
      case tail 𝒢' hD_tl_tl =>
        exact ⟨Δ :: Γ :: 𝒢', HyperEnv.Delete.tail (HyperEnv.Delete.tail hD_tl_tl), .swap ..⟩
  case trans ih1 ih2 =>
    intros E1 H1 hDel1
    obtain ⟨H2, hDel2, hP12⟩ := ih1 hDel1
    obtain ⟨H3, hDel3, hP23⟩ := ih2 hDel2
    exact ⟨H3, hDel3, HyperEnv.Perm.trans hP12 hP23⟩

lemma HyperEnv.Perm.cons_cancel_left {Γ : Env} {𝒢 ℋ : HyperEnv} (hP : Γ :: 𝒢 ~ Γ :: ℋ) :
  𝒢 ~ ℋ := by
  have hDel1 : Delete Γ (Γ :: 𝒢) 𝒢 := Delete.head (List.Perm.refl _)
  obtain ⟨_, hDel2, hP'⟩ := HyperEnv.Perm_Delete hP hDel1
  cases hDel2
  case head _ => exact hP'
  case tail hDel3 =>
    apply HyperEnv.Perm.trans hP'
    exact HyperEnv.Delete_restore hDel3

lemma HyperEnv.Perm_merge_cancel_right {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 → 𝒢 ~ ℋ := by
  intro h
  induction 𝒥 generalizing 𝒢 ℋ
  case nil => simp at h ; exact h
  case cons Γ 𝒥 ih =>
    rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc] at h
    have hcancel := (ih h)
    have h_front : Γ :: 𝒢 ~ Γ :: ℋ := by
      apply HyperEnv.Perm.trans (HyperEnv.Perm_merge_singleton Γ 𝒢).symm
      apply HyperEnv.Perm.trans hcancel
      exact HyperEnv.Perm_merge_singleton Γ ℋ
    exact HyperEnv.Perm.cons_cancel_left h_front

lemma HyperEnv.Perm_merge_cancel_left {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ → 𝒢 ~ ℋ := by
  intro h
  induction 𝒥
  case nil => exact h
  case cons Ξ 𝒥' ih => exact ih (HyperEnv.Perm.cons_cancel_left h)
lemma HyperEnv.disjoint_names_left {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint 𝒢.names S ↔ ∀ Γ ∈ 𝒢, Disjoint Γ.names S := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

lemma HyperEnv.disjoint_names_right {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint S 𝒢.names ↔ ∀ Γ ∈ 𝒢, Disjoint S Γ.names := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

def HyperEnv.Linearity (𝒢 : HyperEnv) : Prop :=
  𝒢.Nodup ∧ 𝒢.PairwiseDisjoint

lemma HyperEnv.Perm_preserves_Linearity {𝒢 ℋ : HyperEnv} :
  𝒢 ~ ℋ → (𝒢.Linearity ↔ ℋ.Linearity) := by
  intro h
  simp [HyperEnv.Linearity, HyperEnv.PairwiseDisjoint]
  rw [HyperEnv.Nodup_perm_iff h, HyperEnv.Perm_PairwiseDisjoint_iff h]

lemma HyperEnv.Perm.preserves_Linearity {𝒢 ℋ : HyperEnv}
  (hP : 𝒢 ~ ℋ) (h : 𝒢.Linearity) : ℋ.Linearity :=
  (HyperEnv.Perm_preserves_Linearity hP).mp h

@[simp] lemma HyperEnv.Linearity_nil :
  HyperEnv.Linearity [] := by simp [HyperEnv.Linearity]

@[simp] lemma HyperEnv.Linearity_singleton {Γ : Env} :
  HyperEnv.Linearity [Γ] = Γ.Nodup := by
  simp [HyperEnv.Linearity, HyperEnv.Nodup]

@[simp] lemma HyperEnv.Linearity_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).Linearity = (𝒢.Linearity ∧ ℋ.Linearity ∧
    ∀ a ∈ 𝒢, ∀ b ∈ ℋ, Disjoint a.names b.names) := by
  simp [HyperEnv.Linearity]
  constructor
  · intro h
    obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
    exact ⟨⟨h1, h3⟩, ⟨⟨h2, h4⟩, h5⟩⟩
  · intro h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
    exact ⟨⟨h1, h3⟩, h2, h4, h5⟩

lemma HyperEnv.Perm_rotate_rhs_right {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ 𝒥 |ₕ 𝒦 → 𝒢 ~ 𝒥 |ₕ 𝒦 |ₕ ℋ := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.trans
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge_assoc
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge_left
      exact HyperEnv.Perm.merge_comm

lemma HyperEnv.Perm_rotate_rhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ 𝒥 |ₕ 𝒦 → 𝒢 ~ 𝒦 |ₕ ℋ |ₕ 𝒥 := by
  intro h
  apply HyperEnv.Perm_rotate_rhs_right
  exact HyperEnv.Perm_rotate_rhs_right h

lemma HyperEnv.Perm_pull_rhs_mid_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ (𝒥 |ₕ 𝒦) → 𝒢 ~ 𝒥 |ₕ (ℋ |ₕ 𝒦) := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.merge_assoc

lemma HyperEnv.Perm_pull_rhs_mid_right {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ (ℋ |ₕ 𝒥) |ₕ 𝒦 → 𝒢 ~ (ℋ |ₕ 𝒦) |ₕ 𝒥 := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.symm
    conv_rhs => rw [HyperEnv.merge_assoc]
    apply HyperEnv.Perm_pull_rhs_mid_left
    conv_rhs => rw [← HyperEnv.merge_assoc]
    apply HyperEnv.Perm_rotate_rhs_left
    rfl

lemma HyperEnv.Perm.exchange_lhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  ℋ ~ 𝒥 → ℋ |ₕ 𝒦 ~ 𝒢 → 𝒥 |ₕ 𝒦 ~ 𝒢 := by
  intros h1 h2
  exact (h2.symm.trans (HyperEnv.Perm.merge_right h1 _)).symm

lemma HyperEnv.Perm.exchange_rhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  ℋ ~ 𝒥 → 𝒢 ~ ℋ |ₕ 𝒦 → 𝒢 ~ 𝒥 |ₕ 𝒦 := by
  intros h1 h2
  exact (h2.trans (HyperEnv.Perm.merge_right h1 _))

lemma Env.exists_perm_cons {Γ : Env} {x : FPName} {A : Types} (h : (x, A) ∈ Γ) :
  ∃ Δ, Γ ~ (x, A) :: Δ := by
  induction Γ
  case nil => simp at h
  case cons e Ξ ih =>
    simp at h
    cases h
    case inl h => subst h ; use Ξ
    case inr h =>
      obtain ⟨y, T⟩ := e
      obtain ⟨Ξ', hP⟩ := ih h
      use (y ∶ T :: Ξ')
      apply List.Perm.trans
      · apply List.Perm.cons
        exact hP
      · apply List.Perm.swap

lemma HyperEnv.Perm_exchange_lhs {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒢 ~ 𝒥 → ℋ ~ 𝒥:= by
   intro h1 h2
   exact h1.symm.trans h2

lemma HyperEnv.Perm_exchange_rhs {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒥 ~ 𝒢 → 𝒥 ~ ℋ := by
   intro h1 h2
   exact h2.trans h1

lemma HyperEnv.Perm_merge_cancel_right_inv {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 := by
  intro h
  induction 𝒥 generalizing 𝒢 ℋ
  case nil => simp ; exact h
  case cons E HE ih =>
    have hG : E :: (𝒢 |ₕ HE) ~ 𝒢 |ₕ E :: HE := HyperEnv.Perm_middle.symm
    have hH : E :: (ℋ |ₕ HE) ~ ℋ |ₕ E :: HE := HyperEnv.Perm_middle.symm
    apply HyperEnv.Perm_exchange_lhs hG
    apply HyperEnv.Perm_exchange_rhs hH
    apply HyperEnv.Perm.cons
    · rfl
    · exact ih h

lemma HyperEnv.Perm_merge_cancel_left_inv {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒢 ~ ℋ → 𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ := by
  intro h
  induction 𝒥
  case nil => exact h
  case cons ih =>
    apply HyperEnv.Perm.cons
    · rfl
    · exact ih

lemma HyperEnv.Perm_merge_comm_assoc_rhs (𝒢 ℋ 𝒥 𝒦 : HyperEnv) :
  𝒢 ~ (ℋ |ₕ (𝒦 |ₕ 𝒥)) → 𝒢 ~ (𝒦 |ₕ (ℋ |ₕ 𝒥)) := by
  intro h
  exact h.trans (HyperEnv.Perm_merge_comm_assoc ℋ 𝒦 𝒥)

lemma HyperEnv.Perm_merge_comm_assoc_lhs (𝒢 ℋ 𝒥 𝒦 : HyperEnv) :
  (ℋ |ₕ (𝒦 |ₕ 𝒥)) ~ 𝒢 → (𝒦 |ₕ (ℋ |ₕ 𝒥)) ~ 𝒢 := by
  intro h
  exact (HyperEnv.Perm_merge_comm_assoc_rhs 𝒢 ℋ 𝒥 𝒦 h.symm).symm

lemma HyperEnv.exists_perm_cons_of_mem {𝒢 : HyperEnv} {Γ : Env} (h : Γ ∈ 𝒢) :
  ∃ 𝒢', 𝒢 ~ Γ :: 𝒢' := by
  induction 𝒢
  case nil => contradiction
  case cons hd tl ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h_in_tl
    · exact ⟨tl, HyperEnv.Perm.refl _⟩
    · obtain ⟨tl', hP⟩ := ih h_in_tl
      use hd :: tl'
      apply HyperEnv.Perm.trans
      · exact HyperEnv.Perm.cons (.refl _) hP
      · exact HyperEnv.Perm.swap hd Γ tl'

lemma HyperEnv.Perm.extract_one_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[z ∶ 1]])
  (h_post : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ)
  (hzx : z ≠ x) (hzy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ',
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ' |ₕ [[z ∶ 1]] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ' := by
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
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], ?_, ?_⟩
      · have := h𝒢_split.symm.trans h𝒢'
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm.merge
        · rw [HyperEnv.cons_append] at h𝒢'
          exact h𝒢'
        · rfl
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] := by
          have h_pre_subst : ([z ∶ 1] :: 𝒢ᵣ') |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~
            𝒢ᵣ |ₕ [[z ∶ 1]] := by
            simp only [HasPerm.perm, List.perm_singleton] at hPE
            subst hPE
            apply HyperEnv.Perm.merge_right (𝒥 := [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) at h𝒢_split
            simp only [← HyperEnv.merge_assoc] at h𝒢_split
            exact h𝒢_split.symm.trans h_pre
          rw [HyperEnv.cons_append, HyperEnv.merge_assoc] at h_pre_subst
          symm at h_pre_subst
          apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          rw [HyperEnv.merge_assoc]
          exact h_pre_subst
        have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
          𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] :=
          h_post.trans h𝒢ᵣ
        have hPΓΓ' : x ∶ A :: Γ' ~ x ∶ A :: Γ := by
          have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEx : (x, A) ∈ E := by
                have := hPE.symm.subset
                simp only [List.cons_subset] at this
                obtain ⟨h1, h2⟩ := this
                exact h1
              have hx𝒢: x ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEx))
              apply hFx hx𝒢
            case inr h =>
              subst h
              apply List.Perm.symm
              exact hPE
          · exfalso
            have hxiny : (x, A) ∈ y ∶ Aᗮ :: Δ := by
              have := hPE.symm.subset
              simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
              exact this.1
            simp only [List.mem_cons, Prod.mk.injEq] at hxiny
            rcases hxiny with heq | hΔ
            · rw [heq.1] at hneq
              contradiction
            · exact hxΔ (Env.mem_pair_fst_in_names _ hΔ)
        have hPΔΔ' : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δ := by
          have hxin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEy : (y, Aᗮ) ∈ E := by
                have := hPE.symm.subset
                simp only [List.cons_subset] at this
                obtain ⟨h1, h2⟩ := this
                exact h1
              have hy𝒢: y ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEy))
              apply hFy hy𝒢
            case inr h =>
              exfalso
              subst h
              have hyinx : (y, Aᗮ) ∈ x ∶ A :: Γ := by
                have := hPE.symm.subset
                simp only [List.cons_subset, List.mem_cons, Prod.mk.injEq] at this ⊢
                exact this.1
              simp only [List.mem_cons, Prod.mk.injEq] at hyinx
              cases hyinx
              case inl h =>
                rw [h.1] at hneq
                contradiction
              case inr h =>
                exact hyΓ (Env.mem_pair_fst_in_names _ h)
          · simp only [HasPerm.perm, List.perm_cons] at hPE ⊢
            exact hPE.symm
        have hPℋ𝒢 : ℋ ~ 𝒢ᵣ' := by
          have hP1 : 𝒢ᵣ' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~
            𝒢ᵣ' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm.merge
              · rfl
              · exact HyperEnv.Perm.cons hPΓΓ'.symm rfl
            · exact HyperEnv.Perm.cons hPΔΔ'.symm rfl
          apply HyperEnv.Perm_merge_cancel_right (𝒥 := [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'])
          simp only [← HyperEnv.merge_assoc]
          exact h_post_subst.trans hP1
        apply HyperEnv.Perm.merge
        · exact hPℋ𝒢
        · apply HyperEnv.Perm.cons
          · apply List.Perm.append
            · exact List.Perm.cons_inv (a := x ∶ A) hPΓΓ'
            · exact List.Perm.cons_inv (a := y ∶ Aᗮ) hPΔΔ'
          · rfl
    case inr h =>
      rw [h] at hPE
      simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
      rw [hPE.1.1] at hzx
      contradiction
  · exfalso
    simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
    rw [hPE.1.1] at hzy
    contradiction

lemma HyperEnv.Perm.extract_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (hzx : z ≠ x) (hzy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hFx' : x ∉ ℋ.names) (hFy' : y ∉ ℋ.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by
  have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · rcases h with hE𝒢 | hEΓx
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ξz : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Ξ, ?_, ?_⟩
      · apply HyperEnv.Perm.trans
        · exact HyperEnv.Perm.merge_right h𝒢Ξz [Γ‚ Δ]
        · have := (HyperEnv.Perm_merge_singleton (z ∶ ⊥ :: Ξ) (𝒢ᵣ' |ₕ [Γ‚ Δ])).symm
          rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
          exact this
      · have h_pre_subst : 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] ~
          ([z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ') |ₕ ([x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ξz h_pre
          exact this.symm
        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post
        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst
        have hEy : y ∶ Aᗮ :: Δ' ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
        obtain ⟨Ey, hEy', hPEy⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hEy
        have hyA: (y ∶ Aᗮ) ∈ Ey := by
            simp [HasPerm.perm] at hPEy
            have := hPEy.symm.subset
            simp at this
            exact this.1
        have hyinEy : y ∈ Ey.names := by
          exact Env.mem_pair_fst_in_names _ hyA
        simp only [List.mem_append, List.mem_singleton] at hEy'
        rcases hEy' with h1 | rfl | rfl | rfl
        · cases h1 with
          | inl h1' =>
            cases h1' with
            | inl hin𝒢ᵣ =>
              exfalso
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem hin𝒢ᵣ) hyinEy]
            | inr hEyΞ =>
              exfalso
              symm at hEyΞ
              subst hEyΞ
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp
              apply Or.inl
              use Aᗮ
              apply (List.Perm.mem_iff (a := (y ∶ Aᗮ)) hPE).mpr
              simp
              exact Or.inr hyA
          | inr hEyΓx =>
            exfalso
            symm at hEyΓx
            subst hEyΓx
            simp only [List.mem_cons] at hyA
            rcases hyA with heq | hyinΓ
            · injection heq with heq_name _
              exact hneq heq_name.symm
            · exact hyΓ (Env.mem_pair_fst_in_names _ hyinΓ)
        · have hPΔΔ' : Δ ~ Δ' := by
            simp [HasPerm.perm] at hPEy
            exact hPEy
          have h_post' : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ] ~
            ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm.cons
            · apply List.Perm.cons
              exact hPΔΔ'
            · rfl
          have h_post_no_y :=
            HyperEnv.Perm_merge_cancel_right (h_post_subst.symm.trans h_post'.symm)
          have hx_LHS : x ∶ A :: Γ' ∈ ℋ |ₕ [x ∶ A :: Γ'] := by simp
          obtain ⟨Ex, hEx_RHS, hPEx⟩ := HyperEnv.Perm_mem h_post_no_y hx_LHS
          have hxA: (x ∶ A) ∈ Ex := by
            simp [HasPerm.perm] at hPEx
            have := hPEx.symm.subset
            simp at this
            exact this.1
          have hxinEx : x ∈ Ex.names := by
            exact Env.mem_pair_fst_in_names _ hxA
          simp only [List.mem_append, List.mem_singleton] at hEx_RHS
          rcases hEx_RHS with h1 | hEx_Xi | rfl
          · cases h1 with
            | inl h =>
              exfalso
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem h) hxinEx]
            | inr h =>
              exfalso
              symm at h
              subst h
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp
              apply Or.inl
              use A
              apply (List.Perm.mem_iff (a := (x ∶ A)) hPE).mpr
              simp
              exact Or.inr hxA
          · have hPΓΓ' : Γ ~ Γ' := by
              simp [HasPerm.perm] at hPEx
              exact hPEx
            have h_post'' : ℋ |ₕ [x ∶ A :: Γ] ~
              ℋ |ₕ [x ∶ A :: Γ'] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp [HasPerm.perm] at hPEx
                apply hPEx
              · rfl
            rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_pull_rhs_mid_left
            rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_left
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm_merge_cancel_right (h_post''.trans h_post_no_y.symm)
            · symm
              apply HyperEnv.Perm.cons
              · exact (List.Perm.append_right Δ hPΓΓ').trans
                  (List.Perm.append_left Γ' hPΔΔ')
              · rfl
    · subst hEΓx
      have hzinΓx : (z, ⊥) ∈ x ∶ A :: Γ := by
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
      rcases hzinΓx with ⟨hzx, _⟩ | hin
      · subst hzx
        contradiction
      · obtain ⟨Γᵣ, hΓ_split⟩ : ∃ Γᵣ, Γ ~ (z, ⊥) :: Γᵣ := Env.exists_perm_cons hin
        refine ⟨𝒢, (Γᵣ ++ Δ), ?_, ?_⟩
        · apply HyperEnv.Perm.merge_left
          exact (HyperEnv.Perm.cons (List.Perm.append_right Δ hΓ_split) (by rfl))
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
            have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ [x ∶ A :: Γ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
              rw [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_comm_assoc
            have hP2 : [x ∶ A :: Γ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] ~ [z ∶ ⊥ :: Ξ] |ₕ 𝒢 |ₕ [y ∶ Aᗮ :: Δ] := by
              apply HyperEnv.Perm.cons
              · exact hPE
              · rfl
            have hP3 : [z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            apply HyperEnv.Perm_merge_cancel_left at this
            exact this
          have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
            𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] := by
            have hP1 := h_post.trans (HyperEnv.Perm.merge_right h𝒢ᵣ [Ξ])
            have hP2 : (𝒢 |ₕ [y ∶ Aᗮ :: Δ] |ₕ [Ξ]) ~ 𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] := by
              have hP1 := hPE.symm.trans (List.Perm.cons (x ∶ A) hΓ_split)
              have hP2 : (x ∶ A :: (z, ⊥) :: Γᵣ) ~ ((z, ⊥) :: x ∶ A :: Γᵣ) := List.Perm.swap ..
              have hP3 := (hP1.trans hP2).cons_inv
              apply HyperEnv.Perm.exchange_rhs_left (ℋ := 𝒢 |ₕ [Ξ])
              · apply HyperEnv.Perm_merge_cancel_left_inv
                · exact HyperEnv.Perm.cons hP3 rfl
              apply HyperEnv.Perm_rotate_rhs_right
              simp only [HyperEnv.merge_assoc]
              apply HyperEnv.Perm_merge_comm_assoc_rhs
              rfl
            exact hP1.trans hP2
          have hPΓ' : Γ' ~ Γᵣ := by
            have hin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hEx, hPEx⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hEx
            rcases hEx with h | rfl | rfl
            · cases h
              case inl h𝒢 =>
                exfalso
                have hxA: (x ∶ A) ∈ E := by
                  simp [HasPerm.perm] at hPEx
                  have := hPEx.symm.subset
                  simp at this
                  exact this.1
                exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
              case inr h =>
                rw [h] at hPEx
                apply List.Perm.cons_inv at hPEx
                simp [HasPerm.perm]
                exact hPEx.symm
            · exfalso
              simp [HasPerm.perm] at hPEx
              have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δ := by
                have := hPEx.symm.subset
                simp at this ⊢
                exact this.1
              simp only [List.mem_cons] at hxin
              rcases hxin with heq | hΔ
              · simp at heq
                exact hneq heq.1
              · exact hxΔ (Env.mem_pair_fst_in_names _ hΔ)
          have hPΔ' : Δ' ~ Δ := by
            have hin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hEy, hPEy⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hEy
            rcases hEy with h | rfl | rfl
            · cases h
              case inl h𝒢 =>
                exfalso
                have hyA: (y ∶ Aᗮ) ∈ E := by
                  simp [HasPerm.perm] at hPEy
                  have := hPEy.symm.subset
                  simp at this
                  exact this.1
                exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
              case inr h =>
                exfalso
                subst h
                simp [HasPerm.perm] at hPEy
                have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γᵣ := by
                  have := hPEy.symm.subset
                  simp at this ⊢
                  exact this.1
                simp only [List.mem_cons] at hyin
                rcases hyin with heq | hΔ
                · simp at heq
                  exact hneq heq.1.symm
                · apply hyΓ
                  have := (Env.mem_pair_fst_in_names _ hΔ)
                  rw [Env.mem_pair_fst_in_names_iff] at this
                  obtain ⟨T, hΓᵣ⟩ := this
                  have hΓᵣz : (y, T) ∈ (z, ⊥) :: Γᵣ :=
                    List.mem_cons_of_mem _ hΓᵣ
                  have hinΓ : (y, T) ∈ Γ :=
                    (List.Perm.mem_iff hΓ_split.symm).mp hΓᵣz
                  rw [Env.mem_pair_fst_in_names_iff]
                  exact ⟨T, hinΓ⟩
            · simp [HasPerm.perm] at hPEy ⊢
              exact hPEy.symm
          have hPℋ𝒢 : ℋ ~ 𝒢 := by
            have hPx : x ∶ A :: Γ' ~ x ∶ A :: Γᵣ := by
              have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']  := by simp
              obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with _ | rfl | rfl
              · exact Env.Perm.cons hPΓ'
              · exact Env.Perm.cons hPΓ'
            have hPy : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δ := by
              have hyin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
              obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hyin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with _ | rfl | rfl
              · exact Env.Perm.cons hPΔ'
              · exact Env.Perm.cons hPΔ'
            have hP1 : 𝒢 |ₕ [x ∶ A :: Γᵣ] |ₕ [y ∶ Aᗮ :: Δ] ~
              𝒢 |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
              apply HyperEnv.Perm.merge
              · exact HyperEnv.Perm.merge rfl (HyperEnv.Perm.cons hPx.symm rfl)
              · exact (HyperEnv.Perm.cons hPy.symm rfl)
            have hP2 := h_post_subst.trans hP1
            apply HyperEnv.Perm_merge_cancel_right at hP2
            apply HyperEnv.Perm_merge_cancel_right at hP2
            exact hP2
          exact HyperEnv.Perm.merge hPℋ𝒢 (HyperEnv.Perm.cons (List.Perm.append hPΓ' hPΔ') rfl)
  · have hzinΔy : (z, ⊥) ∈ y ∶ Aᗮ :: Δ := by
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
    rcases hzinΔy with ⟨hzy, _⟩ | hin
    · subst hzy
      contradiction
    · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (z, ⊥) :: Δᵣ := Env.exists_perm_cons hin
      refine ⟨𝒢, (Γ ++ Δᵣ), ?_, ?_⟩
      · apply HyperEnv.Perm.merge_left
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
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [x ∶ A :: Γ] := by
          have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ [y ∶ Aᗮ :: Δ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ]  := by
            apply HyperEnv.Perm_rotate_rhs_left
            rfl
          have hP2 : [y ∶ Aᗮ :: Δ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ] ~ [z ∶ ⊥ :: Ξ] |ₕ 𝒢 |ₕ  [x ∶ A :: Γ] := by
            apply HyperEnv.Perm.cons
            · exact hPE
            · rfl
          have hP3 : [z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := HyperEnv.Perm.merge_comm
          have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
          apply HyperEnv.Perm_merge_cancel_left at this
          exact this
        have h_post_subst : ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] ~
          𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] := by
          have hP1 := h_post.trans (HyperEnv.Perm.merge_right h𝒢ᵣ [Ξ])
          have hP2 : (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [Ξ]) ~ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] := by
            have hP1 := hPE.symm.trans (List.Perm.cons (y ∶ Aᗮ) hΔ_split)
            have hP2 : (y ∶ Aᗮ :: (z, ⊥) :: Δᵣ) ~ ((z, ⊥) :: y ∶ Aᗮ :: Δᵣ) := List.Perm.swap ..
            have hP3 := (hP1.trans hP2).cons_inv
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm.merge rfl rfl
            · exact HyperEnv.Perm.cons hP3 rfl
          exact hP1.trans hP2
        have hPΓ' : Γ' ~ Γ := by
          have hin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hEx, hPEx⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
          simp only [List.mem_append, List.mem_singleton] at hEx
          rcases hEx with h | rfl | rfl
          · cases h
            case inl h𝒢 =>
              exfalso
              have hxA: (x ∶ A) ∈ E := by
                simp [HasPerm.perm] at hPEx
                have := hPEx.symm.subset
                simp at this
                exact this.1
              exact hFx (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hxA))
            case inr h =>
              rw [h] at hPEx
              apply List.Perm.cons_inv at hPEx
              simp [HasPerm.perm]
              exact hPEx.symm
          · exfalso
            simp [HasPerm.perm] at hPEx
            have hxin : (x ∶ A) ∈ y ∶ Aᗮ :: Δᵣ := by
              have := hPEx.symm.subset
              simp at this ⊢
              exact this.1
            simp only [List.mem_cons] at hxin
            rcases hxin with heq | hΔ
            · simp at heq
              exact hneq heq.1
            · apply hxΔ
              have := (Env.mem_pair_fst_in_names _ hΔ)
              rw [Env.mem_pair_fst_in_names_iff] at this
              obtain ⟨T, hΔᵣz⟩ := this
              have hΔᵣz : (x, T) ∈ (z, ⊥) :: Δᵣ := by
                apply List.mem_cons_of_mem _ hΔᵣz
              have hinΔ : (x, T) ∈ Δ :=
                (List.Perm.mem_iff hΔ_split.symm).mp hΔᵣz
              rw [Env.mem_pair_fst_in_names_iff]
              exact ⟨T, hinΔ⟩
        have hPΔ' : Δ' ~ Δᵣ := by
          have hin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
          obtain ⟨E, hEy, hPEy⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
          simp only [List.mem_append, List.mem_singleton] at hEy
          rcases hEy with h | rfl | rfl
          · cases h
            case inl h𝒢 =>
              exfalso
              have hyA: (y ∶ Aᗮ) ∈ E := by
                simp [HasPerm.perm] at hPEy
                have := hPEy.symm.subset
                simp at this
                exact this.1
              exact hFy (HyperEnv.subset_names_of_mem h𝒢 (Env.mem_pair_fst_in_names _ hyA))
            case inr h =>
              exfalso
              subst h
              simp [HasPerm.perm] at hPEy
              have hyin : (y ∶ Aᗮ) ∈ x ∶ A :: Γ := by
                have := hPEy.symm.subset
                simp at this ⊢
                exact this.1
              simp only [List.mem_cons] at hyin
              rcases hyin with heq | hΔ
              · simp at heq
                exact hneq heq.1.symm
              · apply hyΓ
                have := (Env.mem_pair_fst_in_names _ hΔ)
                rw [Env.mem_pair_fst_in_names_iff] at this
                obtain ⟨T, hΔᵣ⟩ := this
                exact (Env.mem_pair_fst_in_names _ hΔᵣ)
          · simp [HasPerm.perm] at hPEy ⊢
            exact hPEy.symm
        have hPℋ𝒢 : ℋ ~ 𝒢 := by
          have hPx : x ∶ A :: Γ' ~ x ∶ A :: Γ := by
            have hxin : (x ∶ A :: Γ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ']  := by simp
            obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with _ | rfl | rfl
            · exact Env.Perm.cons hPΓ'
            · exact Env.Perm.cons hPΓ'
          have hPy : y ∶ Aᗮ :: Δ' ~ y ∶ Aᗮ :: Δᵣ := by
            have hyin : (y ∶ Aᗮ :: Δ') ∈ ℋ |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by simp
            obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hyin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with _ | rfl | rfl
            · exact Env.Perm.cons hPΔ'
            · exact Env.Perm.cons hPΔ'
          have hP1 : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δᵣ] ~
            𝒢 |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm.merge rfl (HyperEnv.Perm.cons hPx.symm rfl)
            · exact (HyperEnv.Perm.cons hPy.symm rfl)
          have hP2 := h_post_subst.trans hP1
          apply HyperEnv.Perm_merge_cancel_right at hP2
          apply HyperEnv.Perm_merge_cancel_right at hP2
          exact hP2
        exact HyperEnv.Perm.merge hPℋ𝒢 (HyperEnv.Perm.cons (List.Perm.append hPΓ' hPΔ') rfl)

lemma HyperEnv.Perm.extract_one_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {u v x y : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [u ∶ A :: Γ'] |ₕ [v ∶ Aᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (hvΓ : v ∉ Γ.names) (huΔ : u ∉ Δ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by
  have hxin : ([x ∶ 1]) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hxin
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' := h𝒢_split.trans (HyperEnv.Perm.cons hPE (.refl _))
      have h_pre_bot : 𝒢ᵣ' |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ] := by
        have := HyperEnv.Perm.merge_right h𝒢' ([u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ])
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
      obtain ⟨𝒢ᵣ'', Γₙ, h_pre', h_post'⟩ :=
        HyperEnv.Perm.extract_bot_res h_pre_bot h_post hyu hyv hFuᵣ hFvᵣ hFu' hFv' hneq huΔ hvΓ
      refine ⟨𝒢ᵣ'', Γₙ, ?_, h_post'⟩
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

lemma HyperEnv.Perm_nil_inv {𝒢 : HyperEnv} :
  𝒢.Perm [] ↔ 𝒢 = [] := by
  constructor
  · intro h
    generalize h1 : [] = ℋ at h
    induction h <;> simp_all
  · intro h ; subst h ; simp

lemma HyperEnv.Perm_singleton_inv {Γ : Env} {ℋ : HyperEnv} (h : ([Γ] : HyperEnv) ~ ℋ) :
  ∃ Δ, ℋ = [Δ] ∧ Γ ~ Δ := by
  generalize heq : ([Γ] : HyperEnv) = G at h
  induction h generalizing Γ
  case nil => simp only [List.cons_ne_self] at heq
  case cons E1 E2 H1 H2 hPE ih =>
    simp_all only [List.cons.injEq, List.nil_eq, ↓existsAndEq, true_and, and_true,
      List.cons_ne_self, not_isEmpty_of_nonempty, IsEmpty.exists_iff, implies_true]
    obtain ⟨h1, h2⟩ := heq
    subst h1 h2
    exact HyperEnv.Perm_nil_inv.mp hPE.symm
  case swap => simp only [List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at heq
  case trans hP1 hP2 ih1 ih2 =>
    obtain ⟨Δ, hΔ, hP1⟩ := ih1 heq
    obtain ⟨Ξ, hΞ, hP2⟩ := ih2 hΔ.symm
    exact ⟨Ξ, hΞ, hP1.trans hP2⟩

lemma HyperEnv.Perm_singleton_singleton {Γ Δ : Env} :
  ([Γ] : HyperEnv) ~ [Δ] ↔ Γ ~ Δ := by
  constructor
  · intro h
    obtain ⟨Δ', heq, hP⟩ := HyperEnv.Perm_singleton_inv h
    injection heq with hhd
    subst hhd
    exact hP
  · intro h ; exact HyperEnv.Perm.cons h HyperEnv.Perm.nil

lemma HyperEnv.mem_of_mem_mem_names {𝒢 : HyperEnv} {Γ : Env} {x : FPName} {A : Types}
  (h₁ : x ∶ A ∈ Γ) (h₂ : Γ ∈ 𝒢) : x ∈ 𝒢.names := by
  induction 𝒢
  case nil => simp_all only [List.not_mem_nil]
  case cons E HE ih =>
    simp only [List.mem_cons] at h₂
    cases h₂
    case inl h =>
      subst h
      simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
      apply Or.inl
      use A
    case inr h =>
      simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
      apply Or.inr
      apply ih h

lemma HyperEnv.not_mem_names_iff {𝒢 : HyperEnv} {x : FPName} :
  x ∉ 𝒢.names ↔ ∀ (Γ : Env) (A : Types), Γ ∈ 𝒢 → (x, A) ∉ Γ := by
  induction 𝒢
  case nil =>
    simp only [names_nil, Finset.notMem_empty, not_false_eq_true, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  case cons E HE ih =>
    constructor
    · intro h1 Γ A hin
      simp only [names_cons, Finset.mem_union, not_or, List.mem_cons] at h1 hin
      obtain ⟨hE, hHE⟩ := h1
      cases hin
      case inl h =>
        subst h
        exact Env.not_mem_names_iff.mp hE A
      case inr h =>
        exact ih.mp hHE Γ A h
    · intro h
      have h' := h E
      simp only [List.mem_cons, true_or, forall_const, names_cons, Finset.mem_union,
        Env.mem_pair_fst_in_names_iff, not_or, not_exists] at h h' ⊢
      constructor
      · have := Env.not_mem_names_iff.mpr h'
        simp only [Env.mem_pair_fst_in_names_iff, not_exists] at this
        exact this
      · apply ih.mpr
        intro Γ A hin
        exact h Γ A (Or.inr hin)

lemma HyperEnv.PairwiseDisjoint_tail_not_in_head {𝒢 ℋ : HyperEnv} :
  List.Pairwise Env.disjoint (𝒢 |ₕ ℋ) →
  (∀ E, E ∈ ℋ → ∀ x A, (x ∶ A) ∈ E → x ∉ 𝒢.names) := by
  intros h Γ hΓinℋ x A hinΓ hxin𝒢
  have h_cross := (List.pairwise_append.mp h).2.2
  obtain ⟨B, Δ, hinΔ, hΔin𝒢⟩ := HyperEnv.mem_pair_fst_in_names.mp hxin𝒢
  have hxΓ : x ∈ Γ.names := Env.mem_pair_fst_in_names _ hinΓ
  have hxΔ : x ∈ Δ.names := Env.mem_pair_fst_in_names _ hinΔ
  have hD := h_cross Δ hΔin𝒢 Γ hΓinℋ
  exact Finset.disjoint_left.mp hD hxΔ hxΓ

lemma HyperEnv.substNames_res_left
  {𝒢 : HyperEnv} {Γ Δ : Env} {x z w : FPName} {A B : Types}
  (hx𝒢 : x ∉ 𝒢.names) (hxΓ : x ∉ Γ.names) (hxΔ : x ∉ Δ.names) (hxw : x ≠ w) :
  ∀ Ξ ∈ 𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (x, C) ∈ Ξ → x = z := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hx𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
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

lemma HyperEnv.substNames_res_right
  {𝒢 : HyperEnv} {Γ Δ : Env} {x y w : FPName} {A B : Types}
  (hy𝒢 : y ∉ 𝒢.names) (hyΓ : y ∉ Γ.names) (hyΔ : y ∉ Δ.names) (hyx : y ≠ x) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (y, C) ∈ Ξ → y = w := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hy𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
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


lemma HyperEnv.mem_names_subset_of_perm {𝒢 : HyperEnv} {E Γ Δ : Env} {x : FPName} {A : Types}
  (hE𝒢 : E ∈ 𝒢) (hPE : E ~ x ∶ A :: Γ‚ Δ) :
  Γ.names ⊆ 𝒢.names ∧ Δ.names ⊆ 𝒢.names := by
  have hNames := HyperEnv.names_eq_of_perm (HyperEnv.Perm_singleton_singleton.mpr hPE)
  simp at hNames
  have hΓsub : Γ.names ⊆ 𝒢.names := by
    have hs1 : (Γ.names ∪ Δ.names) ⊆ insert x (Γ.names ∪ Δ.names) := Finset.subset_insert _ _
    have hs2 : Γ.names ⊆ (Γ.names ∪ Δ.names) := Finset.subset_union_left
    have := hs2.trans hs1
    rw [← hNames] at this
    exact this.trans (HyperEnv.subset_names_of_mem hE𝒢)
  have hΔsub : Δ.names ⊆ 𝒢.names := by
    have hs1 : (Γ.names ∪ Δ.names) ⊆ insert x (Γ.names ∪ Δ.names) := Finset.subset_insert _ _
    have hs2 : Δ.names ⊆ (Γ.names ∪ Δ.names) := Finset.subset_union_right
    have := hs2.trans hs1
    rw [← hNames] at this
    exact this.trans (HyperEnv.subset_names_of_mem hE𝒢)
  exact ⟨hΓsub, hΔsub⟩

lemma HyperEnv.Perm.extract_tensor_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Γ'' Δ Δ' Δ'' : Env} {u v x w : FPName} {A B C : Types}
  (h_pre : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ])
  (h_post : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~ 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ])
  (hxw : x ≠ w) (hux : u ≠ x) (huw : u ≠ w) (hvx : v ≠ x) (hvw : v ≠ w)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (huΔ' : u ∉ Δ'.names) (hvΓ' : v ∉ Γ'.names) :
   ∃ 𝒢ₙ Γₙ Δₙ,
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ] ∧
    ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [w ∶ A :: Γₙ] |ₕ [x ∶ B :: Δₙ] := by
  have h1 : (x ∶ A ⨂ B :: Γ‚ Δ) ∈ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | hh
  · rcases h with hE𝒢 | hEΓu
    · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
      have h𝒢Ξz : 𝒢 ~ (x ∶ A ⨂ B :: Γ‚ Δ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ'‚ Δ'], Γ, Δ, ?_, ?_⟩
      · apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        rw [← HyperEnv.cons_append]
        exact h𝒢Ξz
      · have h_pre_subst : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] ~
          ([x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ') |ₕ ([u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ']) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ξz h_pre
          exact this.symm
        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        simp only [HyperEnv.merge_assoc] at h_post
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post
        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst
        have hEv : v ∶ Cᗮ :: Δ'' ∈ ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by simp
        obtain ⟨Ey, hEy', hPEy⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hEv
        have hyC : (v ∶ Cᗮ) ∈ Ey := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEy).mpr (by simp)
        have hyinEy : v ∈ Ey.names := Env.mem_pair_fst_in_names _ hyC
        simp only [List.mem_append, List.mem_singleton] at hEy'
        rcases hEy' with h1 | rfl | rfl | rfl
        · cases h1 with
          | inl h1' =>
            cases h1' with
            | inl hin𝒢ᵣ =>
              exfalso
              apply hFv
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem hin𝒢ᵣ) hyinEy]
            | inr hEyΞ =>
              rcases hEyΞ with rfl | rfl
              · simp at hyinEy
                rcases hyinEy with rfl | h2
                · exfalso ; apply hvw ; rfl
                · exfalso
                  have ⟨hΓsub, _⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFv (hΓsub (Env.mem_pair_fst_in_names_iff.mpr h2))
              · simp at hyinEy
                rcases hyinEy with rfl | h2
                · exfalso ; apply hvx ; rfl
                · exfalso
                  have ⟨_, hΔsub⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFv (hΔsub (Env.mem_pair_fst_in_names_iff.mpr h2))
          | inr hEyΓx =>
            exfalso
            symm at hEyΓx
            subst hEyΓx
            simp only [List.mem_cons] at hyC
            rcases hyC with heq | hyinΓ
            · injection heq with heq_name _
              exact hneq heq_name.symm
            · exact hvΓ' (Env.mem_pair_fst_in_names _ hyinΓ)
        · have hPΔ'Δ'' : Δ' ~ Δ'' := by
            simp [HasPerm.perm] at hPEy
            exact hPEy
          have h_post' : ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ']) ~
            ℋ |ₕ ([u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'']) := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm_merge_cancel_left_inv
            rw [HyperEnv.Perm_singleton_singleton]
            apply List.Perm.cons
            exact hPΔ'Δ''
          have h_post_no_v := by
            have ht := h_post_subst.symm.trans h_post'.symm
            simp only [← HyperEnv.merge_assoc] at ht
            apply HyperEnv.Perm_merge_cancel_right at ht
            exact ht
          have huRHS : u ∶ C :: Γ'' ∈ ℋ |ₕ [u ∶ C :: Γ''] := by simp
          obtain ⟨Eu, hEuLHS, hPEu⟩ := HyperEnv.Perm_mem h_post_no_v huRHS
          have huinEu : u ∈ Eu.names := by
            have huC: (u ∶ C) ∈ Eu := by
              simp [HasPerm.perm] at hPEu
              have := hPEu.symm.subset
              simp at this
              exact this.1
            exact Env.mem_pair_fst_in_names _ huC
          simp only [List.mem_append, List.mem_singleton] at hEuLHS
          rcases hEuLHS with h1 | hExΞ | rfl
          · cases h1 with
            | inl h =>
              exfalso
              apply hFu
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              rcases h with hin | rfl
              · simp [(HyperEnv.subset_names_of_mem hin) huinEu]
              · exfalso
                simp at huinEu
                rcases huinEu with rfl | hin
                · apply huw ; rfl
                · have ⟨hΓ, _⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                  exact hFu (hΓ (Env.mem_pair_fst_in_names_iff.mpr hin))
            | inr h =>
              exfalso
              subst h
              simp at huinEu
              rcases huinEu with rfl | hin
              · apply hux ; rfl
              · have ⟨_, hΔ⟩ := HyperEnv.mem_names_subset_of_perm hE𝒢 hPE
                exact hFu (hΔ (Env.mem_pair_fst_in_names_iff.mpr hin))
          · have hPΓ'Γ'' : Γ' ~ Γ'' := by
              simp [HasPerm.perm] at hPEu
              exact hPEu
            have h_post'' : ℋ |ₕ [u ∶ C :: Γ'] ~
              ℋ |ₕ [u ∶ C :: Γ''] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp [HasPerm.perm] at hPEu
                apply hPEu
              · rfl
            have ht := h_post''.trans h_post_no_v.symm
            apply HyperEnv.Perm_merge_cancel_right at ht
            rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm_rotate_rhs_right
              exact ht
            · symm
              apply HyperEnv.Perm.cons
              · exact (List.Perm.append_right Δ' hPΓ'Γ'').trans
                  (List.Perm.append_left Γ'' hPΔ'Δ'')
              · rfl
    · subst hEΓu
      have hxin := (List.Perm.mem_iff (a := x ∶ A ⨂ B) hPE).mpr (by simp)
      simp at hxin
      rcases hxin with ⟨rfl, rfl⟩ | h
      · exfalso ; apply hux ; rfl
      · obtain ⟨Ξ, hPΓ'⟩ : ∃ Ξ, Γ' ~ (x, A ⨂ B) :: Ξ :=
          Env.exists_perm_cons h
        have hPE_no_x : u ∶ C :: Ξ ~ Γ‚ Δ := by
          have h1 := hPE.symm.trans (List.Perm.cons (u ∶ C) hPΓ')
          have h2 : (u ∶ C :: (x, A ⨂ B) :: Ξ) ~ ((x, A ⨂ B) :: u ∶ C :: Ξ) := List.Perm.swap ..
          exact (h1.trans h2).cons_inv.symm
        have huin : (u, C) ∈ Γ‚ Δ :=
          (List.Perm.mem_iff (a := u ∶ C) hPE_no_x ).mp (by simp)
        simp at huin
        rcases huin with huΓ | huΔ
        · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (u, C) :: Γᵣ := Env.exists_perm_cons huΓ
          have hPΞ : Ξ ~ Γᵣ‚ Δ := List.Perm.cons_inv (hPE_no_x.trans (List.Perm.append_right Δ hPΓ))
          refine ⟨𝒢, (Γᵣ‚ Δ'), Δ, ?_, ?_⟩
          · apply HyperEnv.Perm.merge
            · rfl
            · apply HyperEnv.Perm_singleton_singleton.mpr
              rw [← List.cons_append]
              have hP1 : x ∶ A ⨂ B :: Γᵣ‚ Δ‚ Δ' ~ x ∶ A ⨂ B :: Γᵣ‚ Δ'‚ Δ := by
                simp
                apply List.Perm.cons
                apply List.Perm.append_left
                exact List.perm_append_comm
              have hP2 := List.Perm.append (t₂ := Δ') (by
                have : (x ∶ A ⨂ B :: Ξ) ~ (x ∶ A ⨂ B :: Γᵣ‚ Δ) := by
                  apply List.Perm.cons
                  exact hPΞ
                exact hPΓ'.trans this) (by rfl)
              exact hP2.trans hP1
          · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
                [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_comm_assoc
              have hP2 : [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] ~
                [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                apply HyperEnv.Perm.cons hPE rfl
              have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
                HyperEnv.Perm.merge_comm
              have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
              exact HyperEnv.Perm_merge_cancel_left this
            have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [v ∶ Cᗮ :: Δ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
            have hPΔ'' : Δ'' ~ Δ' := by
              have hin : (v ∶ Cᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
              obtain ⟨E, hE, hPEv⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with h | rfl | h_wx
              · rcases h with h𝒢 | rfl
                · rcases h𝒢 with h1 | h2
                  · exfalso
                    have hvA: (v ∶ Cᗮ) ∈ E := (List.Perm.mem_iff hPEv).mpr (by simp)
                    exact hFv (HyperEnv.subset_names_of_mem h1
                      (Env.mem_pair_fst_in_names _ hvA))
                  · rw [h2] at hPEv
                    apply List.Perm.cons_inv at hPEv
                    exact hPEv.symm
                · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                  simp at hvin
                  rcases hvin with ⟨rfl, rfl⟩ | hvΓ
                  · exfalso ; apply hvw ; rfl
                  · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΓ]
                    have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                      (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                    simp at hin2
                    exfalso
                    rcases hin2 with ⟨rfl, _⟩ | hvΞ
                    · apply hneq ; rfl
                    · have h3 : (v, Cᗮ) ∈ Γ' :=
                        (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                      exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
              · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                simp at hvin
                exfalso
                rcases hvin with ⟨rfl, rfl⟩ | hvΔ
                · apply hvx  ; rfl
                · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΔ]
                  have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                    (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                  simp at hin2
                  rcases hin2 with ⟨rfl, _⟩ | hvΞ
                  · apply hneq ; rfl
                  · have h3 : (v, Cᗮ) ∈ Γ' :=
                      (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
            have h_post_no_v : ℋ |ₕ [u ∶ C :: Γ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_rotate_rhs_right at h_post_subst
              rw [← HyperEnv.merge_assoc] at h_post_subst
              have : [v ∶ Cᗮ :: Δ''] ~ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact Env.Perm.cons hPΔ''
              have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _) this
              exact HyperEnv.Perm_merge_cancel_right (hLHS.symm.trans (h_post_subst))
            have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := u ∶ C :: Γ'')
              h_post_no_v.symm (by simp)
            simp at hE1
            rcases hE1 with h𝒢 | rfl | rfl
            · exfalso
              have huΓ := (List.Perm.mem_iff (a := u ∶ C) hPE1).mpr (by simp)
              exact hFu (HyperEnv.mem_of_mem_mem_names huΓ h𝒢)
            · have hPΓ'' : Γ'' ~ w ∶ A :: Γᵣ := by
                have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) hPΓ)
                have h2 : (w ∶ A :: u ∶ C :: Γᵣ) ~ (u ∶ C :: w ∶ A :: Γᵣ) := List.Perm.swap ..
                exact List.Perm.cons_inv (h1.trans h2)
              have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] := by
                have : 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [u ∶ C :: Γ''] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                  apply HyperEnv.Perm_rotate_rhs_right
                  apply HyperEnv.Perm.merge
                  · apply HyperEnv.Perm_merge_comm
                  · rw [HyperEnv.Perm_singleton_singleton]
                    exact hPE1.symm
                exact HyperEnv.Perm_merge_cancel_right (h_post_no_v.trans this.symm)
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm.merge
              · exact hℋ.trans HyperEnv.Perm_merge_comm
              · rw [HyperEnv.Perm_singleton_singleton]
                rw [← List.cons_append, Env.merge]
                exact List.Perm.append hPΓ'' hPΔ''
            · exfalso
              have h_post_subst2 : ℋ |ₕ [u ∶ C :: Γ''] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] :=
                  HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                    (HyperEnv.Perm_singleton_singleton.mpr hPE1)
                exact h_post_no_v.trans this
              have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := HyperEnv.Perm_merge_cancel_right h_post_subst2
              have hwin: w ∶ A :: Γ ∈ 𝒢 |ₕ [w ∶ A :: Γ] := by simp
              obtain ⟨E, hE, hPEw⟩ := HyperEnv.Perm_mem hℋ hwin
              have huEw : u ∶ C ∈ w ∶ A :: Γ := List.mem_cons_of_mem _ huΓ
              have huE := (List.Perm.mem_iff (a := u ∶ C) hPEw).mpr huEw
              exact hFu' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ huE))
        · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (u, C) :: Δᵣ := Env.exists_perm_cons huΔ
          have hPΞ : Ξ ~ Γ‚ Δᵣ := by
            have h1 := hPE_no_x.trans (List.Perm.append_left Γ hΔ_split)
            exact List.Perm.cons_inv (h1.trans List.perm_middle)
          refine ⟨𝒢, Γ, (Δᵣ ++ Δ'), ?_, ?_⟩
          · apply HyperEnv.Perm.merge_left
            apply HyperEnv.Perm.cons
            · have h1 := List.Perm.append_right Δ' hPΓ'
              have h2 : ((x, A ⨂ B) :: Ξ) ++ Δ' ~ (x, A ⨂ B) :: (Ξ ++ Δ') := by rfl
              have h3 : (x, A ⨂ B) :: (Ξ ++ Δ') ~ (x, A ⨂ B) :: ((Γ ++ Δᵣ) ++ Δ') :=
                List.Perm.cons _ (List.Perm.append_right Δ' hPΞ)
              have h4 : (x, A ⨂ B) :: ((Γ ++ Δᵣ) ++ Δ') ~ (x, A ⨂ B) :: (Γ ++ (Δᵣ ++ Δ')) := by
                rw [List.append_assoc]
              exact h1.trans (h2.trans (h3.trans h4))
            · rfl
          · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
              have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
                [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.merge_assoc]
                apply HyperEnv.Perm_merge_comm_assoc
              have hP2 : [u ∶ C :: Γ'] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] ~
                [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [v ∶ Cᗮ :: Δ'] := by
                apply HyperEnv.Perm.cons hPE rfl
              have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
                HyperEnv.Perm.merge_comm
              have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
              exact HyperEnv.Perm_merge_cancel_left this
            have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [v ∶ Cᗮ :: Δ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [v ∶ Cᗮ :: Δ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
            have hPΔ'' : Δ'' ~ Δ' := by
              have hin : (v ∶ Cᗮ :: Δ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
              obtain ⟨E, hE, hPEv⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
              simp only [List.mem_append, List.mem_singleton] at hE
              rcases hE with h | rfl | h_wx
              · rcases h with h𝒢 | rfl
                · rcases h𝒢 with h1 | h2
                  · exfalso
                    have hvA: (v ∶ Cᗮ) ∈ E := (List.Perm.mem_iff hPEv).mpr (by simp)
                    exact hFv (HyperEnv.subset_names_of_mem h1
                      (Env.mem_pair_fst_in_names _ hvA))
                  · rw [h2] at hPEv
                    apply List.Perm.cons_inv at hPEv
                    exact hPEv.symm
                · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                  simp at hvin
                  rcases hvin with ⟨rfl, rfl⟩ | hvΓ
                  · exfalso ; apply hvw ; rfl
                  · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΓ]
                    have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                      (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                    simp at hin2
                    exfalso
                    rcases hin2 with ⟨rfl, _⟩ | hvΞ
                    · apply hneq ; rfl
                    · have h3 : (v, Cᗮ) ∈ Γ' :=
                        (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                      exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
              · have hvin := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEv).mpr (by simp)
                simp at hvin
                exfalso
                rcases hvin with ⟨rfl, rfl⟩ | hvΔ
                · apply hvx  ; rfl
                · have hin1 : (v, Cᗮ) ∈ Γ‚ Δ := by simp [hvΔ]
                  have hin2 : (v, Cᗮ) ∈ u ∶ C :: Ξ :=
                    (List.Perm.mem_iff hPE_no_x.symm).mp hin1
                  simp at hin2
                  rcases hin2 with ⟨rfl, _⟩ | hvΞ
                  · apply hneq ; rfl
                  · have h3 : (v, Cᗮ) ∈ Γ' :=
                      (List.Perm.mem_iff hPΓ').mpr (by simp [hvΞ])
                    exact hvΓ' (Env.mem_pair_fst_in_names _ h3)
            have h_post_no_v : ℋ |ₕ [u ∶ C :: Γ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              apply HyperEnv.Perm_rotate_rhs_left
              apply HyperEnv.Perm_rotate_rhs_right at h_post_subst
              rw [← HyperEnv.merge_assoc] at h_post_subst
              have : [v ∶ Cᗮ :: Δ''] ~ [v ∶ Cᗮ :: Δ'] := by
                rw [HyperEnv.Perm_singleton_singleton]
                exact Env.Perm.cons hPΔ''
              have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
                ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ'] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _) this
              exact HyperEnv.Perm_merge_cancel_right (hLHS.symm.trans (h_post_subst))
            have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := u ∶ C :: Γ'')
              h_post_no_v.symm (by simp)
            simp at hE1
            rcases hE1 with h𝒢 | rfl | rfl
            · exfalso
              have huΔ := (List.Perm.mem_iff (a := u ∶ C) hPE1).mpr (by simp)
              exact hFu (HyperEnv.mem_of_mem_mem_names huΔ h𝒢)
            · exfalso
              have h_post_subst2 : ℋ |ₕ [u ∶ C :: Γ''] ~
                𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] :=
                  HyperEnv.Perm.merge
                    (HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                      (HyperEnv.Perm_singleton_singleton.mpr hPE1))
                    (HyperEnv.Perm.refl _)
                exact h_post_no_v.trans this
              have hRHS_rot : 𝒢 |ₕ [u ∶ C :: Γ''] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [x ∶ B :: Δ] |ₕ [u ∶ C :: Γ''] := by
                symm
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm_merge_cancel_right_inv
                apply HyperEnv.Perm.trans (HyperEnv.Perm_merge_comm).symm
                rfl
              have hℋ := HyperEnv.Perm_merge_cancel_right (h_post_subst2.trans hRHS_rot)
              have hxin: x ∶ B :: Δ ∈ 𝒢 |ₕ [x ∶ B :: Δ] := by simp
              obtain ⟨E, hE, hPEx⟩ := HyperEnv.Perm_mem hℋ hxin
              have huEx : u ∶ C ∈ x ∶ B :: Δ := List.mem_cons_of_mem _ huΔ
              have huE := (List.Perm.mem_iff (a := u ∶ C) hPEx).mpr huEx
              exact hFu' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ huE))
            · have hPΓ'' : Γ'' ~ x ∶ B :: Δᵣ := by
                have h1 := hPE1.symm.trans (List.Perm.cons (x ∶ B) hΔ_split)
                have h2 : (x ∶ B :: u ∶ C :: Δᵣ) ~ (u ∶ C :: x ∶ B :: Δᵣ) := List.Perm.swap ..
                exact List.Perm.cons_inv (h1.trans h2)
              have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := by
                have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                  𝒢 |ₕ [w ∶ A :: Γ] |ₕ [u ∶ C :: Γ''] := by
                  apply HyperEnv.Perm.merge
                  · rfl
                  · rw [HyperEnv.Perm_singleton_singleton]
                    exact hPE1
                exact HyperEnv.Perm_merge_cancel_right (h_post_no_v.trans this)
              apply HyperEnv.Perm.merge
              · exact hℋ
              · rw [HyperEnv.Perm_singleton_singleton]
                rw [← List.cons_append]
                exact List.Perm.append hPΓ'' hPΔ''
  · subst hh
    have hxin := (List.Perm.mem_iff (a := x ∶ A ⨂ B) hPE).mpr (by simp)
    simp at hxin
    rcases hxin with ⟨rfl, _⟩ | h
    · exfalso ; apply hvx ; rfl
    · obtain ⟨Ξ, hPΔ'⟩ : ∃ Ξ, Δ' ~ (x, A ⨂ B) :: Ξ := Env.exists_perm_cons h
      have hPE_no_x : v ∶ Cᗮ :: Ξ ~ Γ‚ Δ := by
        have h1 := hPE.symm.trans (List.Perm.cons (v ∶ Cᗮ) hPΔ')
        have h2 : (v ∶ Cᗮ :: (x, A ⨂ B) :: Ξ) ~ ((x, A ⨂ B) :: v ∶ Cᗮ :: Ξ) := List.Perm.swap ..
        exact (h1.trans h2).cons_inv.symm
      have hvin : (v, Cᗮ) ∈ Γ‚ Δ :=
        (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE_no_x ).mp (by simp)
      simp at hvin
      rcases hvin with hΓ | hΔ
      · obtain ⟨Γᵣ, hPΓ⟩ : ∃ Γᵣ, Γ ~ (v, Cᗮ) :: Γᵣ := Env.exists_perm_cons hΓ
        have hPΞ : Ξ ~ Γᵣ‚ Δ := List.Perm.cons_inv (hPE_no_x.trans (List.Perm.append_right Δ hPΓ))
        refine ⟨𝒢, (Γ'‚ Γᵣ), Δ, ?_, ?_⟩
        · apply HyperEnv.Perm.merge
          · rfl
          · apply HyperEnv.Perm_singleton_singleton.mpr
            have hP1 : x ∶ A ⨂ B :: Γ'‚ Γᵣ‚ Δ ~ x ∶ A ⨂ B :: Γ'‚ Ξ := by
              apply List.Perm.cons
              rw [Env.merge_assoc]
              apply List.Perm.append
              · rfl
              · exact hPΞ.symm
            have hP2 : x ∶ A ⨂ B :: Γ'‚ Ξ ~ Γ'‚ (x ∶ A ⨂ B :: Ξ) := List.perm_middle.symm
            have hP3 : Γ'‚ (x ∶ A ⨂ B :: Ξ) ~ Γ'‚ Δ' := by
              apply List.Perm.append
              · rfl
              · exact hPΔ'.symm
            exact ((hP1.trans hP2).trans hP3).symm
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
              [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.merge_assoc]
            have hP2 : [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] ~
              [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm.cons hPE rfl
            have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
              HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            exact HyperEnv.Perm_merge_cancel_left this
          have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                (𝒢 |ₕ [u ∶ C :: Γ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
                exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
              exact h_post.trans this
          have hPΓ'' : Γ'' ~ Γ' := by
            have hin : (u ∶ C :: Γ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
            obtain ⟨E, hE, hPEu⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with h | rfl | hwx
            · rcases h with h𝒢 | rfl
              · rcases h𝒢 with h1 | h2
                · exfalso
                  have huA: (u ∶ C) ∈ E := (List.Perm.mem_iff hPEu).mpr (by simp)
                  exact hFu (HyperEnv.subset_names_of_mem h1 (Env.mem_pair_fst_in_names _ huA))
                · rw [h2] at hPEu
                  exact (List.Perm.cons_inv hPEu).symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
                simp at huin
                rcases huin with ⟨rfl, rfl⟩ | huΓ
                · apply huw ; rfl
                · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΓ])
                  simp at huin
                  rcases huin with ⟨rfl, _⟩ | huΞ
                  · apply hneq ; rfl
                  · apply huΔ'
                    apply Env.mem_pair_fst_in_names_iff.mpr
                    use C
                    exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, rfl⟩ | huΔ
              · apply hux ; rfl
              · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΔ])
                simp at huin
                rcases huin with ⟨rfl, _⟩ | huΞ
                · apply hneq ; rfl
                · apply huΔ'
                  apply Env.mem_pair_fst_in_names_iff.mpr
                  use C
                  exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
          have h_post_no_u : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have hPeq : [u ∶ C :: Γ''] ~ [u ∶ C :: Γ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact Env.Perm.cons hPΓ''
            have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ''] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPeq)
                (HyperEnv.Perm.refl _)
            have hP1 := h_post_subst.symm.trans hLHS
            apply HyperEnv.Perm_rotate_rhs_left at hP1
            symm at hP1
            apply HyperEnv.Perm_rotate_rhs_right at hP1
            rw [← HyperEnv.merge_assoc] at hP1
            have hP2 := HyperEnv.Perm_merge_cancel_right hP1
            apply HyperEnv.Perm_rotate_rhs_left at hP2
            symm at hP2
            exact (hP2.trans HyperEnv.Perm.merge_comm).symm
          have ⟨E1, hE1, hPE1⟩ := HyperEnv.Perm_mem (Γ := v ∶ Cᗮ :: Δ'') h_post_no_u.symm (by simp)
          simp at hE1
          rcases hE1 with h𝒢 | rfl | rfl
          · exfalso
            have hvΓ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE1).mpr (by simp)
            exact hFv (HyperEnv.mem_of_mem_mem_names hvΓ h𝒢)
          · have hPΔ'' : Δ'' ~ w ∶ A :: Γᵣ := by
              have h1 := hPE1.symm.trans (List.Perm.cons (w ∶ A) hPΓ)
              have h2 : (w ∶ A :: v ∶ Cᗮ :: Γᵣ) ~ (v ∶ Cᗮ :: w ∶ A :: Γᵣ) := List.Perm.swap ..
              exact List.Perm.cons_inv (h1.trans h2)
            have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] := by
              have : 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Cᗮ :: Δ''] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
                apply HyperEnv.Perm_rotate_rhs_right
                apply HyperEnv.Perm.merge
                · apply HyperEnv.Perm_merge_comm
                · rw [HyperEnv.Perm_singleton_singleton]
                  exact hPE1.symm
              exact HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this.symm)
            apply HyperEnv.Perm_rotate_rhs_right
            apply HyperEnv.Perm.merge
            · exact hℋ.trans HyperEnv.Perm_merge_comm
            · rw [HyperEnv.Perm_singleton_singleton]
              rw [← List.cons_append]
              have hP1 : Γ'' ++ w ∶ A :: Γᵣ ~ Γ' ++ w ∶ A :: Γᵣ := by
                apply List.Perm.append
                · exact hPΓ''
                · rfl
              have hP3 : Γ'' ++ Δ'' ~ Γ'' ++ w ∶ A :: Γᵣ := by
                apply List.Perm.append
                · rfl
                · exact hPΔ''
              rw [List.cons_append]
              exact (hP3.trans hP1).trans List.perm_middle
          · exfalso
            have h_post_subst2 : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
              𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] := by
              have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] :=
                HyperEnv.Perm.merge (HyperEnv.Perm.refl _)
                  (HyperEnv.Perm_singleton_singleton.mpr hPE1)
              exact h_post_no_u.trans this
            have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := HyperEnv.Perm_merge_cancel_right h_post_subst2
            have hwin: w ∶ A :: Γ ∈ 𝒢 |ₕ [w ∶ A :: Γ] := by simp
            obtain ⟨E, hE, hPEw⟩ := HyperEnv.Perm_mem hℋ hwin
            have hvEw : v ∶ Cᗮ ∈ w ∶ A :: Γ := List.mem_cons_of_mem _ hΓ
            have hvE := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEw).mpr hvEw
            exact hFv' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ hvE))
      · obtain ⟨Δᵣ, hPΔ⟩ : ∃ Δᵣ, Δ ~ (v, Cᗮ) :: Δᵣ := Env.exists_perm_cons hΔ
        have hPΞ : Ξ ~ Γ‚ Δᵣ := by
          have h1 := hPE_no_x.trans (List.Perm.append_left Γ hPΔ)
          exact List.Perm.cons_inv (h1.trans List.perm_middle)
        refine ⟨𝒢, Γ, (Γ'‚ Δᵣ), ?_, ?_⟩
        · apply HyperEnv.Perm.merge
          · rfl
          · apply HyperEnv.Perm_singleton_singleton.mpr
            have hP1 : x ∶ A ⨂ B :: (Γ'‚ Γ)‚ Δᵣ ~ x ∶ A ⨂ B :: Γ'‚ (Γ‚ Δᵣ) := by
              apply List.Perm.cons
              rw [Env.merge_assoc]
            have hP2 : x ∶ A ⨂ B :: Γ'‚ (Γ‚ Δᵣ) ~ x ∶ A ⨂ B :: Γ'‚ Ξ := by
              apply List.Perm.cons
              apply List.Perm.append
              · rfl
              · exact hPΞ.symm
            have hP3 : x ∶ A ⨂ B :: Γ'‚ Ξ ~ Γ'‚ (x ∶ A ⨂ B :: Ξ) := List.perm_middle.symm
            have hP4 : Γ'‚ (x ∶ A ⨂ B :: Ξ) ~ Γ'‚ Δ' := by
              apply List.Perm.append
              · rfl
              · exact hPΔ'.symm
            have ht : Γ'‚ Δ' ~ x ∶ A ⨂ B :: Γ'‚ Γ‚ Δᵣ :=
              (((hP1.trans hP2).trans hP3).trans hP4).symm
            have hP5 : x ∶ A ⨂ B :: Γ'‚ Γ‚ Δᵣ ~ x ∶ A ⨂ B :: Γ‚ (Γ'‚ Δᵣ) := by
              apply List.Perm.cons
              simp
              apply List.perm_append_comm_assoc
            exact ht.trans hP5
        · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢 |ₕ [u ∶ C :: Γ'] := by
            have hP1 : 𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ'] ~
              [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm_rotate_rhs_left
              rw [HyperEnv.merge_assoc]
            have hP2 : [v ∶ Cᗮ :: Δ'] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] ~
              [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢 |ₕ [u ∶ C :: Γ'] := by
              apply HyperEnv.Perm.cons hPE rfl
            have hP3 : [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ 𝒢ᵣ ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] :=
              HyperEnv.Perm.merge_comm
            have := hP3.trans (h_pre.symm.trans (hP1.trans hP2))
            exact HyperEnv.Perm_merge_cancel_left this
          have h_post_subst : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [u ∶ C :: Γ'] |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have : 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
              (𝒢 |ₕ [u ∶ C :: Γ']) |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
              rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
              exact HyperEnv.Perm.merge_exchange_left h𝒢ᵣ
            exact h_post.trans this
          have hPΓ'' : Γ'' ~ Γ' := by
            have hin : (u ∶ C :: Γ'') ∈ ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] := by simp
            obtain ⟨E, hE, hPEu⟩ := HyperEnv.Perm_mem h_post_subst.symm hin
            simp only [List.mem_append, List.mem_singleton] at hE
            rcases hE with h | rfl | hwx
            · rcases h with h𝒢 | rfl
              · rcases h𝒢 with h1 | h2
                · exfalso
                  have huA: (u ∶ C) ∈ E := (List.Perm.mem_iff hPEu).mpr (by simp)
                  exact hFu (HyperEnv.subset_names_of_mem h1 (Env.mem_pair_fst_in_names _ huA))
                · rw [h2] at hPEu
                  exact (List.Perm.cons_inv hPEu).symm
              · exfalso
                have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
                simp at huin
                rcases huin with ⟨rfl, rfl⟩ | huΓ
                · apply huw ; rfl
                · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΓ])
                  simp at huin
                  rcases huin with ⟨rfl, _⟩ | huΞ
                  · apply hneq ; rfl
                  · apply huΔ'
                    apply Env.mem_pair_fst_in_names_iff.mpr
                    use C
                    exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
            · exfalso
              have huin := (List.Perm.mem_iff (a := u ∶ C) hPEu).mpr (by simp)
              simp at huin ; rcases huin with ⟨rfl, rfl⟩ | huΔ
              · apply hux ; rfl
              · have huin := (List.Perm.mem_iff (a := u ∶ C) hPE_no_x).mpr (by simp [huΔ])
                simp at huin
                rcases huin with ⟨rfl, _⟩ | huΞ
                · apply hneq ; rfl
                · apply huΔ'
                  apply Env.mem_pair_fst_in_names_iff.mpr
                  use C
                  exact ((List.Perm.mem_iff (a := u ∶ C) hPΔ').mpr (by simp [huΞ]))
          have h_post_no_u : ℋ |ₕ [v ∶ Cᗮ :: Δ''] ~
            𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] := by
            have hPeq : [u ∶ C :: Γ''] ~ [u ∶ C :: Γ'] := by
              rw [HyperEnv.Perm_singleton_singleton]
              exact Env.Perm.cons hPΓ''
            have hLHS : ℋ |ₕ [u ∶ C :: Γ''] |ₕ [v ∶ Cᗮ :: Δ''] ~
              ℋ |ₕ [u ∶ C :: Γ'] |ₕ [v ∶ Cᗮ :: Δ''] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPeq)
                (HyperEnv.Perm.refl _)
            have hP1 := h_post_subst.symm.trans hLHS
            apply HyperEnv.Perm_rotate_rhs_left at hP1
            symm at hP1
            apply HyperEnv.Perm_rotate_rhs_right at hP1
            rw [← HyperEnv.merge_assoc] at hP1
            have hP2 := HyperEnv.Perm_merge_cancel_right hP1
            apply HyperEnv.Perm_rotate_rhs_left at hP2
            symm at hP2
            exact (hP2.trans HyperEnv.Perm.merge_comm).symm
          have ⟨E1, hE1, hPE1⟩ :=
            HyperEnv.Perm_mem (Γ := v ∶ Cᗮ :: Δ'') h_post_no_u.symm (by simp)
          simp at hE1
          rcases hE1 with h𝒢 | rfl | rfl
          · exfalso
            have hvΔ := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPE1).mpr (by simp)
            exact hFv (HyperEnv.mem_of_mem_mem_names hvΔ h𝒢)
          · exfalso
            have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~ 𝒢 |ₕ [x ∶ B :: Δ] |ₕ [v ∶ Cᗮ :: Δ''] := by
              symm
              apply HyperEnv.Perm_rotate_rhs_right
              apply HyperEnv.Perm.merge
              · exact HyperEnv.Perm_merge_comm
              · rw [HyperEnv.Perm_singleton_singleton]
                exact hPE1.symm
            have hℋ : ℋ ~ 𝒢 |ₕ [x ∶ B :: Δ] :=
              HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this)
            have hxin : x ∶ B :: Δ ∈ 𝒢 |ₕ [x ∶ B :: Δ] := by simp
            obtain ⟨E, hE, hPEx⟩ := HyperEnv.Perm_mem hℋ hxin
            have hvEx : v ∶ Cᗮ ∈ x ∶ B :: Δ := List.mem_cons_of_mem _ hΔ
            have hvE := (List.Perm.mem_iff (a := v ∶ Cᗮ) hPEx).mpr hvEx
            exact hFv' (HyperEnv.subset_names_of_mem hE (Env.mem_pair_fst_in_names _ hvE))
          · have hPΔ'' : Δ'' ~ x ∶ B :: Δᵣ := by
              have h1 := hPE1.symm.trans (List.Perm.cons (x ∶ B) hPΔ)
              have h2 : (x ∶ B :: v ∶ Cᗮ :: Δᵣ) ~ (v ∶ Cᗮ :: x ∶ B :: Δᵣ) := List.Perm.swap ..
              exact List.Perm.cons_inv (h1.trans h2)
            have hℋ : ℋ ~ 𝒢 |ₕ [w ∶ A :: Γ] := by
              have : 𝒢 |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ] ~
                𝒢 |ₕ [w ∶ A :: Γ] |ₕ [v ∶ Cᗮ :: Δ''] := by
                apply HyperEnv.Perm.merge
                · rfl
                · rw [HyperEnv.Perm_singleton_singleton]
                  exact hPE1
              exact HyperEnv.Perm_merge_cancel_right (h_post_no_u.trans this)
            apply HyperEnv.Perm.merge
            · exact hℋ
            · exact HyperEnv.Perm_singleton_singleton.mpr
                ((List.Perm.append hPΓ'' hPΔ'').trans List.perm_middle)















lemma HyperEnv.Perm.extract_parr_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Γ'' Δ Δ' Δ'' : Env} {u v y w : FPName} {A B T : Types}
  (h_pre : 𝒢 |ₕ [u ∶ T :: Γ'] |ₕ [v ∶ Tᗮ :: Δ'] ~ 𝒢ᵣ |ₕ [y ∶ A ⅋ B :: Γ])
  (h_post : ℋ |ₕ [u ∶ T :: Γ''] |ₕ [v ∶ Tᗮ :: Δ''] ~ 𝒢ᵣ |ₕ [w ∶ A :: y ∶ B :: Γ])
  (hyw : y ≠ w) (huy : u ≠ y) (huw : u ≠ w) (hvy : v ≠ y) (hvw : v ≠ w)
  : ∃ 𝒢ₙ Γₙ,
    𝒢 |ₕ [Γ'‚ Δ'] ~ 𝒢ₙ |ₕ [y ∶ A ⅋ B :: Γₙ] ∧
    ℋ |ₕ [Γ''‚ Δ''] ~ 𝒢ₙ |ₕ [w ∶ A :: y ∶ B :: Γₙ] := by sorry





-- FIXME: Move to TypingStep
-- lemma TypingStepₘ_inv_tensor_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
--   {x w : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
--   (hStep : TypingStepₘ 𝒟 (x⟦w⟧) 𝒟') :
--   ∃ 𝒢ᵣ Γ Δ A B,
--     (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ‚ Δ]) ∧
--     (𝒢' ~ 𝒢ᵣ |ₕ [w ∶ A :: Γ] |ₕ [x ∶ B :: Δ]) := by sorry

-- lemma TypingStepₘ_inv_parr_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
--   {y w : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
--   (hStep : TypingStepₘ 𝒟 (y⸨w⸩) 𝒟') :
--   ∃ 𝒢ᵣ Γ A B,
--     (𝒢 ~ 𝒢ᵣ |ₕ [y ∶ A ⅋ B :: Γ]) ∧
--     (𝒢' ~ 𝒢ᵣ |ₕ [w ∶ A :: y ∶ B :: Γ]) := by sorry















-- FIXME: Delete (unsused)
-- lemma HyperEnv.Perm.extract_one_res_source
--   {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ : Env} {x y z : FPName} {A : Types}
--   (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[z ∶ 1]])
--   (hxz : x ≠ z) (hyz : y ≠ z) :
--   ∃ 𝒢ᵣ_new,
--     𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[z ∶ 1]] := by
--   have hzin : ([z ∶ 1]) ∈ 𝒢ᵣ |ₕ [[z ∶ 1]] := by
--     simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
--   obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hzin
--   simp only [List.mem_append, List.mem_singleton] at hE
--   rcases hE with h | rfl | rfl
--   · cases h
--     case inl h =>
--       obtain ⟨𝒢ᵣ', h𝒢_split⟩ : ∃ 𝒢ᵣ, 𝒢 ~ E :: 𝒢ᵣ :=
--         HyperEnv.exists_perm_cons_of_mem h
--       have h𝒢' : 𝒢 ~ [z ∶ 1] :: 𝒢ᵣ' := by
--         apply HyperEnv.Perm.trans h𝒢_split
--         exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
--       refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], ?_⟩
--       have := h𝒢_split.symm.trans h𝒢'
--       apply HyperEnv.Perm_rotate_rhs_right
--       apply HyperEnv.Perm.merge
--       · rw [HyperEnv.cons_append] at h𝒢'
--         exact h𝒢'
--       · rfl
--     case inr h =>
--       rw [h] at hPE
--       simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
--       rw [hPE.1.1] at hxz
--       contradiction
--   · exfalso
--     simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
--     rw [hPE.1.1] at hyz
--     contradiction

-- lemma HyperEnv.Perm.extract_bot_res_source
--   {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ Ξ : Env} {x y z : FPName} {A : Types}
--   (h_pre : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
--   (hxz : x ≠ z) (hyz : y ≠ z)
--   (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
--   (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
--   ∃ 𝒢ᵣ_new Γᵣ,
--     𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γᵣ] := by
--   have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
--   obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
--   simp only [List.mem_append, List.mem_singleton] at hE
--   rcases hE with h | rfl | rfl
--   · rcases h with hE𝒢 | hEΓx
--     · obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem hE𝒢
--       have h𝒢Ξz : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢ᵣ' := by
--         apply HyperEnv.Perm.trans h𝒢_split
--         exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
--       refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Ξ, ?_⟩
--       apply HyperEnv.Perm.trans
--       · exact HyperEnv.Perm.merge_right h𝒢Ξz [Γ‚ Δ]
--       · have := (HyperEnv.Perm_merge_singleton (z ∶ ⊥ :: Ξ) (𝒢ᵣ' |ₕ [Γ‚ Δ])).symm
--         rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
--         exact this
--     · subst hEΓx
--       have hzinΓx : (z, ⊥) ∈ x ∶ A :: Γ := by
--         simp [HasPerm.perm] at hPE
--         have h := hPE.symm.subset
--         simp at h
--         obtain ⟨hL, hR⟩ := h
--         cases hL
--         case inl hL1 =>
--           rw [hL1.1, hL1.2]
--           simp
--         case inr hL2 =>
--           exact List.mem_cons.mpr (Or.inr hL2)
--       simp at hzinΓx
--       rcases hzinΓx with ⟨hzx_eq, _⟩ | hin
--       · subst hzx_eq
--         contradiction
--       · obtain ⟨Γᵣ, hΓ_split⟩ : ∃ Γᵣ, Γ ~ (z, ⊥) :: Γᵣ := Env.exists_perm_cons hin
--         refine ⟨𝒢, (Γᵣ ++ Δ), ?_⟩
--         apply HyperEnv.Perm.merge_left
--         exact (HyperEnv.Perm.cons (List.Perm.append_right Δ hΓ_split) (by rfl))
--   · have hzinΔy : (z, ⊥) ∈ y ∶ Aᗮ :: Δ := by
--       simp [HasPerm.perm] at hPE
--       have h := hPE.symm.subset
--       simp at h
--       obtain ⟨hL, hR⟩ := h
--       cases hL
--       case inl hL1 =>
--         rw [hL1.1, hL1.2]
--         simp
--       case inr hL2 =>
--         exact List.mem_cons.mpr (Or.inr hL2)
--     simp at hzinΔy
--     rcases hzinΔy with ⟨hzy_eq, _⟩ | hin
--     · subst hzy_eq
--       contradiction
--     · obtain ⟨Δᵣ, hΔ_split⟩ : ∃ Δᵣ, Δ ~ (z, ⊥) :: Δᵣ := Env.exists_perm_cons hin
--       refine ⟨𝒢, (Γ ++ Δᵣ), ?_⟩
--       apply HyperEnv.Perm.merge_left
--       apply HyperEnv.Perm.cons
--       · have hP1 := List.Perm.append_right Γ hΔ_split
--         have hP2 : Γ ++ Δ ~ Δ ++ Γ := by
--           simp [HasPerm.perm]
--           apply List.perm_append_comm
--         have hP3 : ((z, ⊥) :: Δᵣ ++ Γ) ~ ((z, ⊥) :: Γ ++ Δᵣ) := by
--           apply List.Perm.cons
--           exact List.perm_append_comm
--         exact (hP2.trans hP1).trans hP3
--       · rfl

-- lemma HyperEnv.Perm.extract_one_bot_res_source
--   {𝒢 𝒢ᵣ : HyperEnv} {Γ Δ Ξ : Env} {u v x y : FPName} {A : Types}
--   (h_pre : 𝒢 |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ])
--   (hux : u ≠ x) (hvx : v ≠ x) (huy : u ≠ y) (hvy : v ≠ y)
--   (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
--   (hneq : u ≠ v) (hvΓ : v ∉ Γ.names) (huΔ : u ∉ Δ.names) :
--   ∃ 𝒢ᵣ_new Γᵣ,
--     𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by
--   have hxin : ([x ∶ 1]) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
--   obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hxin
--   simp only [List.mem_append, List.mem_singleton] at hE
--   rcases hE with h | rfl | rfl
--   · cases h
--     case inl h =>
--       obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem h
--       have h𝒢' := h𝒢_split.trans (HyperEnv.Perm.cons hPE (.refl _))
--       have h_pre_bot : 𝒢ᵣ' |ₕ [u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ] ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ] := by
--         have := HyperEnv.Perm.merge_right h𝒢' ([u ∶ A :: Γ] |ₕ [v ∶ Aᗮ :: Δ])
--         rw [← HyperEnv.merge_assoc] at this
--         have := this.symm.trans h_pre
--         apply HyperEnv.Perm_rotate_rhs_right at this
--         rw [HyperEnv.merge_assoc, ← HyperEnv.cons_append, ← HyperEnv.cons_append] at this
--         apply HyperEnv.Perm.cons_cancel_left at this
--         rw [← HyperEnv.merge_nilR (𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ])]
--         apply HyperEnv.Perm_rotate_rhs_left
--         simp only [List.append_eq, List.cons_append, List.nil_append,
--           List.append_assoc, List.append_nil] at ⊢ this
--         exact this
--       simp only [HasPerm.perm, List.perm_singleton] at hPE
--       subst hPE
--       have hFuᵣ : u ∉ HyperEnv.names 𝒢ᵣ':= by
--         intro hc
--         exact hFu (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
--       have hFvᵣ : v ∉ HyperEnv.names 𝒢ᵣ' := by
--         intro hc
--         exact hFv (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])
--       obtain ⟨𝒢ᵣ'', Γₙ, h_pre'⟩ :=
--         HyperEnv.Perm.extract_bot_res_source h_pre_bot huy hvy hFuᵣ hFvᵣ hneq huΔ hvΓ
--       refine ⟨𝒢ᵣ'', Γₙ, ?_⟩
--       · have h1 := HyperEnv.Perm.merge_right h𝒢_split ([Γ‚ Δ])
--         have h2 := HyperEnv.Perm.merge_right h_pre' ([[x ∶ 1]])
--         conv_rhs at h1 => rw [HyperEnv.cons_append]
--         apply HyperEnv.Perm_rotate_rhs_right at h1
--         conv_rhs at h2 => rw [HyperEnv.merge_assoc]
--         apply HyperEnv.Perm_pull_rhs_mid_left at h2
--         rw [← HyperEnv.merge_assoc] at h2
--         apply HyperEnv.Perm_rotate_rhs_right at h2
--         exact h1.trans h2
--     case inr h =>
--       subst h
--       simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
--       obtain ⟨⟨h1, _⟩, _⟩ := hPE
--       subst h1
--       contradiction
--   · simp only [HasPerm.perm, List.perm_singleton, List.cons.injEq, Prod.mk.injEq] at hPE
--     obtain ⟨⟨h1, _⟩, _⟩ := hPE
--     subst h1
--     contradiction
