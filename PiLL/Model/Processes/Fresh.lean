import PiLL.Model.Processes.Names

def freshName (s : Finset FPName) : FPName :=
  s.sup id + 1

lemma fresh_is_fresh (s : Finset FPName) (x : FPName) (h : x ∈ s) :
  id x < freshName s := by
  have hxle : x ≤ s.sup id := by
    have : id x ≤ s.sup id := Finset.le_sup h
    exact this
  exact Nat.lt_succ_of_le hxle

lemma exists_one_fresh (L : Finset FPName) :
  ∃u, u ∉ L := by
  let u := freshName L
  use u
  intro hc
  have h_lt := fresh_is_fresh L u hc
  exact Nat.lt_irrefl _ h_lt

lemma exists_two_fresh (L : Finset FPName) :
  ∃ u v, u ∉ L ∧ v ∉ L ∧ u ≠ v := by
  let u := freshName L
  have hu : u ∉ L := by
    intro hc
    have h_lt := fresh_is_fresh L u hc
    exact Nat.lt_irrefl _ h_lt
  let v := freshName (L ∪ {u})
  have hv : v ∉ L := by
    intro hc
    have hin : v ∈ L ∪ {u} := Finset.mem_union_left {u} hc
    have h_lt := fresh_is_fresh (L ∪ {u}) v hin
    exact Nat.lt_irrefl _ h_lt
  have hneq : u ≠ v := by
    intro heq
    have hinu : v ∈ ({u} : Finset FPName) := by rw [← heq] ; simp
    have hinLu : v ∈ L ∪ {u} := by rw [← heq] ; simp
    have h_lt := fresh_is_fresh (L ∪ {u}) v hinLu
    exact Nat.lt_irrefl _ h_lt
  refine ⟨u, v, hu, hv, hneq⟩
