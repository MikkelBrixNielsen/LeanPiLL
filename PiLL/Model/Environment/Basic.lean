import PiLL.Model.Processes.LocalClosure
import PiLL.Model.STypes.Subst

abbrev Elem := (FPName × Types)

abbrev Elem.mk (x : FPName) (A : Types) : Elem := (x, A)
infixr:68 " ∶ " => Elem.mk

abbrev Env := List Elem

def Env.names (Γ : Env) : Finset FPName :=
  (Γ.map Prod.fst).toFinset

abbrev Env.merge (Γ Δ : Env) : Env := Γ ++ Δ
infixl:69 "‚ " => Env.merge -- uses \glq to avoid clashing with the actual comma

def Env.Nodup (Γ : Env) : Prop := (Γ.map Prod.fst).Nodup

@[simp] def Env.disjoint (Γ Δ : Env) : Prop :=
  Disjoint Γ.names Δ.names

def Env.serverUsable (Γ : Env) : Prop :=
  ∀p, p ∈ Γ → (p.snd).isServerUsable
prefix:max "?ₑ" => Env.serverUsable

def Env.freeTypes (Γ : Env) :=
  Γ.foldl (fun acc (_, A) => acc ∪ A.freeTypes) ∅
notation "ft(" Γ ")ₑ" => Env.freeTypes Γ

def Env.lc (k : Nat) (Γ : Env) : Prop :=
  ∀ x A, (x, A) ∈ Γ → A.lc k

def Env.shiftTypes (d c : Nat) (Γ : Env) : Env :=
  Γ.map (fun (x, A) => (x, A.shift d c))

instance : HasShift Env where shift Γ d c := Env.shiftTypes d c Γ

def Env.substNames (Γ : Env) (R T : FPName) : Env :=
  Γ.map (fun (x, A) => if x == T then (R, A) else (x, A))

instance : HasSubst Env FPName FPName where subst := Env.substNames

def Env.substTypes (Γ : Env) (A : Types) (k : Nat) : Env :=
  Γ.map (fun (x, B) => (x, B.subst A k))

instance : HasSubst Env Types Nat where subst := Env.substTypes

lemma Env.merge_unitL (Γ : Env) : ∅‚ Γ = Γ := by simp

lemma Env.merge_unitR (Γ : Env) : Γ‚ ∅ = Γ := by simp

lemma Env.cons_nil {e : Elem} : e :: ∅ = [e] := by simp

lemma Env.cons_empty {e : Elem} : e :: [] = [e] := by simp

lemma Env.merge_comm (Γ Δ : Env) : List.Perm (Γ‚ Δ) (Δ‚ Γ) := by
  exact List.perm_append_comm

lemma Env.merge_assoc (Γ Δ Ξ : Env) : Γ‚ Δ‚ Ξ = Γ‚ (Δ‚ Ξ) := by
  simp [Env.merge]

instance : HasPerm Env where perm := List.Perm
