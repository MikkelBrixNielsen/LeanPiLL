import PiLL.Model.STypes.Subst
import PiLL.Model.STypes.Properties
import PiLL.Model.STypes.Notation

theorem Types.dual_neq (A : Types) : A ≠ Aᗮ := by
  cases A <;> simp [dual]

theorem Types.dual_inj (A B : Types) : Aᗮ = Bᗮ ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem Types.dual_involution (A : Types) : Aᗮᗮ = A := by
  induction A <;> simp [Types.dual, *]

lemma Types.lc_dual {n : Nat} {A : Types} :
  A.lc n ↔  Aᗮ.lc n :=
  by induction A generalizing n <;> simp_all [Types.lc, Types.dual]

-- (A ↑ᵗ d, c).lc (n + c + d) ↔ A.lc (n + d)
lemma Types.lc_shift_c_inv {n d c : Nat} {A : Types} :
  (A.shift d c).lc (n + c + d) ↔ A.lc (n + d) := by
  induction A generalizing n d c <;> simp_all only [Types.shift, Types.lc]
  case var v | varDual v => cases v <;> grind [TVar.lc, TVar.shift]
  case forall_ ih | exists_ ih => exact ih (d := d + 1)

lemma Types.lc_le {n m : Nat} {A : Types} (h : n ≤ m) :
  A.lc n → A.lc m := by
  induction A generalizing n m <;> simp_all [Types.lc, TVar.lc] <;> grind

lemma Types.lc_mono {n : Nat} {A : Types} :
  A.lc 0 → A.lc n := by
  intro hlc
  exact Types.lc_le (n := 0) (m := n) (by simp) hlc

-- A.lc n → (A ↑ᵗ d, c).lc (n + c)
lemma Types.lc_shift {n d c : Nat} {A : Types} :
  A.lc n → (A.shift d c).lc (n + c) := by
  induction A generalizing n d c <;>
    simp_all [Types.shift, TVar.shift, Types.lc, TVar.lc] <;> grind

-- A.lc n → (A ↑ᵗ 0, 1).lc (n + 1)
lemma Types.lc_shift_0 {n : Nat} {A : Types} :
  A.lc n → (A.shift 0 1).lc (n + 1) := by
  intro h ; apply Types.lc_shift h

-- B{A // k}.lc (n + k) ↔ B.lc (n + k + 1)
lemma Types.lc_subst_inv {n k : Nat} {A B : Types} (hA : A.lc (n + k)) :
  (B.subst A k).lc (n + k) ↔ B.lc (n + k + 1) := by
  induction B generalizing n k A <;> simp_all only [Types.subst, Types.lc, TVar.lc]
  case forall_ B ih | exists_ B ih => exact ih (k := k + 1) (Types.lc_shift_0 hA)
  case var v | varDual v => grind [Types.subst, Types.lc, TVar.lc, Types.lc_dual]

-- A.lc n → ((B{A // 0}).lc n ↔ B.lc (n + 1))
lemma Types.lc_subst_inv_0 {n : Nat} {A B : Types} (hA : A.lc n) :
  ((B.subst A 0).lc n ↔ B.lc (n + 1)) := by
  exact Types.lc_subst_inv (k := 0) hA

-- (A ↑ᵗ d, 1).lc (n + d + 1) ↔ A.lc (n + d)
lemma Types.lc_shift_inv {n d : Nat} {A : Types} :
  (A.shift d 1).lc (n + d + 1) ↔ A.lc (n + d) := by
  induction A generalizing n d <;> simp_all only [Types.lc, Types.shift]
  case var v | varDual v => cases v <;> grind [TVar.shift, TVar.lc]
  case forall_ ihA | exists_ ihA => exact ihA (d := d + 1)

-- A⁺ᵗ.lc (n + 1) ↔ A.lc n
lemma Types.lc_shift_inv_0 {n : Nat} {A : Types} :
  (A.shift 0 1).lc (n + 1) ↔ A.lc n := Types.lc_shift_inv (d := 0)

-- (A ↑ᵗ d, m) ↑ᵗ d, n = (A ↑ᵗ d, n) ↑ᵗ d, m
lemma Types.lc_shift_comm {A : Types} {d m n : Nat} :
  (A.shift d m).shift d n = (A.shift d n).shift d m := by
  induction A generalizing d m n <;> simp [Types.shift] <;> simp_all [TVar.shift] <;> grind

-- A⁺ᵗ ↑ᵗ k = (A ↑ᵗ k)⁺ᵗ
lemma Types.lc_shift_comm_0 {A : Types} {k : Nat} :
  (A.shift 0 1).shift 0 k = (A.shift 0 k).shift 0 1 := Types.lc_shift_comm (d := 0)

-- (A ↑ᵗ d, a) ↑ᵗ d, b = A ↑ᵗ d, (a + b)
lemma Types.shift_add {A : Types} {d a b : Nat} :
  (A.shift d a).shift d b = A.shift d (a + b) := by
  induction A generalizing d a b <;>
    simp_all only [Types.shift, var.injEq, varDual.injEq, TVar.shift]
  case var v | varDual v => cases v <;> grind

-- (A ↑ᵗ d, a) ↑ᵗ (d + a), b = A ↑ᵗ d, (a + b)
lemma Types.shift_accum {A : Types} {d a b : Nat} :
  (A.shift d a).shift (d + a) b = A.shift d (a + b) := by
  induction A generalizing d a b <;> simp [Types.shift, TVar.shift] <;> try grind
  case var v | varDual v => cases v <;> grind

lemma Types.shift_accum_0 {A : Types} {a b : Nat} :
  (A.shift 0 a).shift a b = A.shift 0 (a + b) := by
  have := Types.shift_accum (d := 0) (a := a) (b := b) (A := A)
  simp_all

-- (Aᗮ ↑ᵗ d, c) = (A ↑ᵗ d, c)ᗮ
lemma Types.shift_dual_comm {A : Types} {d c : Nat} :
  ((A.dual).shift d c) = (A.shift d c).dual := by
  induction A generalizing d c <;> simp_all [Types.shift, Types.dual, TVar.shift]

lemma Types.shift_dual_comm_notation {A : Types} {d c : Nat} :
  (Aᗮ ↑ᵗ d, c) = (A ↑ᵗ d, c)ᗮ := by
  induction A generalizing d c <;>
    simp_all [HasShiftTypes.shift, Types.shift, Types.dual, TVar.shift]

--  (A ↑ᵗ i, 1) ↑ᵗ (d + 1 + i), c = (A ↑ᵗ (d + i), c) ↑ᵗ i, 1
lemma Types.shift_comm {A : Types} {d c i : Nat} :
  (A.shift i 1).shift (d + 1 + i) c = (A.shift (d + i) c).shift i 1 := by
  induction A generalizing d c i <;>
    simp_all only [Types.shift, TVar.shift, forall_.injEq, exists_.injEq]
  case var v | varDual v => cases v <;> grind
  case forall_ ih | exists_ ih => exact ih (d := d) (c := c) (i := i + 1)

-- (A ↑ᵗ 1) ↑ᵗ (d + 1), c = (A.↑ᵗ d, c) ↑ᵗ 1
lemma Types.shift_comm_0 {A : Types} {d c : Nat} :
 (A.shift 0 1).shift (d + 1) c = (A.shift d c).shift 0 1 := Types.shift_comm (i := 0)

-- (B{A // k}) ↑ᵗ d, c = (B ↑ᵗ (d + 1), c){(A ↑ᵗ d, c) // k}
lemma Types.shift_subst_comm_depth_ge_idx {A B : Types} {d c i : Nat} (hle : i ≤ d) :
  (B.subst A i).shift d c = (B.shift (d + 1) c).subst (A.shift d c) i := by
  induction B generalizing d c i A <;> simp only [Types.shift, Types.subst] <;>
    try simp_all only [Nat.add_le_add_iff_right, forall_.injEq, exists_.injEq]
  case var v | varDual v =>
    cases v with
    | bound =>
      simp [Types.subst]
      split_ifs <;> grind [Types.shift, TVar.shift, Types.subst, Types.shift_dual_comm]
    | free => rfl
  case forall_ B ih | exists_ => grind [Types.shift_comm_0]

-- (B{A // 0}) ↑ᵗ d, c = (B ↑ᵗ (d + 1), c){(A ↑ᵗ d, c) // 0}
lemma Types.shift_subst_0_comm {A B : Types} {d c : Nat} :
  (B.subst A 0).shift d c = (B.shift (d + 1) c).subst (A.shift d c) 0 :=
  Types.shift_subst_comm_depth_ge_idx (by simp)

-- B{A // i} ↑ᵗ d, c = (B ↑ᵗ d, c){(A ↑ᵗ d, c) // (i + c)}
lemma Types.shift_subst_comm_depth_le_idx {A B : Types} {d c i : Nat} (hle : d ≤ i) :
  (B.subst A i).shift d c = (B.shift d c).subst (A.shift d c) (i + c) := by
  induction B generalizing A d c i <;>
    simp_all only [Types.shift, Types.subst, Nat.add_le_add_iff_right, forall_.injEq, exists_.injEq]
  case var v | varDual v =>
    cases v with
    | bound =>
      simp [TVar.shift]
      split_ifs <;> grind [Types.shift_dual_comm, Types.shift, Types.subst, TVar.shift]
    | free => rfl
  case forall_ ih | exists_ ih => grind [Types.shift_comm_0]

-- B{A // i} ↑ᵗ c = (B ↑ᵗ c){(A ↑ᵗ c) // (i + c)}
lemma Types.shift_0_subst_comm {A B : Types} {c i : Nat} :
  (B.subst A i).shift 0 c = (B.shift 0 c).subst (A.shift 0 c) (i + c) :=
  Types.shift_subst_comm_depth_le_idx (by simp)

@[simp] lemma Types.isServerUsable_shift {d c : Nat} {A : Types} :
  A.isServerUsable ↔ (A ↑ᵗ d, c).isServerUsable := by
  cases A <;> simp [HasShiftTypes.shift, Types.shift, Types.isServerUsable]

lemma Types.lc_subst_lc_eq_lc_gen {A B : Types} {n n' k : Nat} :
  n' ≤ n → k ≤ n → Types.lc n B → Types.lc n' A → Types.lc n (B.subst A k) := by
  intro hle1 hle2 hB hA
  induction B generalizing n n' A k <;> try grind [Types.lc, TVar.lc, Types.subst]
  case var v | varDual v => cases v <;>
    grind [Types.lc, TVar.lc, Types.subst, Types.lc_dual, Types.lc_le]
  case forall_ ih | exists_ ih =>
    exact ih (by simp_all) (by simp_all) hB (Types.lc_shift hA)

lemma Types.lc_subst_lc_eq_lc {A B : Types} {n k : Nat} :
  Types.lc (n + 1) B → Types.lc n A → k ≤ n → Types.lc n (B.subst A k) := by
  intro hB hA hk
  induction B generalizing n k hk A <;>
    simp_all only [Types.lc, TVar.lc, Types.subst, Types.lc_shift,
      and_self, Nat.add_le_add_iff_right]
  case var v | varDual v => grind [Types.lc, Types.subst, TVar.lc, Types.lc_dual]

lemma Types.isServerUsable_subst {T A : Types} {k : Nat} (h : T.isServerUsable) :
  (T.subst A k).isServerUsable := by
  cases T <;> simp_all [Types.isServerUsable, Types.subst]

lemma Types.subst_dual_comm {A B : Types} {k : Nat} :
  (B.subst A k).dual = (B.dual).subst A k := by
  induction B generalizing A k <;> simp_all only [Types.subst, Types.dual]
  case var v |varDual v =>
    cases v <;> grind [Types.subst, Types.dual, Types.dual_involution]

@[simp] lemma Types.shift_subst_cancel {A B : Types} {d : Nat} :
  (A.shift d 1).subst B d = A := by
  induction A generalizing d B <;> simp_all only [Types.shift, Types.subst]
  case var v | varDual v => cases v <;> grind [TVar.shift, Types.subst]

@[simp] lemma Types.shiftTypes_substTypes_cancel_0 {A B : Types} :
  B⁺ᵗ{A // 0} = B := Types.shift_subst_cancel (A := B) (B := A) (d := 0)

-- B{A' // d}{A // i} = B{A ↑ᵗ d, 1 // i + 1}{A'{A // i} // d}
lemma Types.subst_comm {A A' B : Types} {d i : Nat} (hle : d ≤ i) :
  (B.subst A' d).subst A i = (B.subst (A.shift d 1) (i + 1)).subst (A'.subst A i) d := by
  induction B generalizing A A' d i hle <;>
    try simp_all only [Types.subst, Nat.add_le_add_iff_right, forall_.injEq, exists_.injEq]
  case forall_ ih | exists_ ih => rw [Types.shift_comm_0, Types.shift_0_subst_comm]
  case var v | varDual v =>
    cases v <;> (
      simp_all only [Types.subst, beq_iff_eq, gt_iff_lt] <;> (
        grind [Types.subst, Types.shift_subst_cancel, Types.subst_dual_comm,
          Types.dual_involution]
      )
    )

  -- B{A' // 0}{A // k} = B{A ↑ᵗ 0, 1 // k + 1}{A'{A // k} // 0}
lemma Types.subst_comm_0 {A A' B : Types} {i : Nat} :
  (B.subst A' 0).subst A i = (B.subst (A.shift 0 1) (i + 1)).subst (A'.subst A i) 0 :=
    Types.subst_comm (by simp)

@[simp] lemma Types.subst_dual_comm_notation {A B : Types} {i : Nat} :
  Bᗮ{A // i} = B{A // i}ᗮ := by
  simp only [HasSubst.subst]
  rw [Types.subst_dual_comm]
