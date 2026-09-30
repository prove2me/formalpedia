-- Prove2me | solution 1 for lean_workbook_plus_3883
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:37:03.546507+00:00
-- url     : https://prove2.me/submissions/c9f7ad6f-57db-4d0e-b39d-20c4d341060b

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

def FiveLetterEdge (v w : Fin 5) : Prop := 3 ≤ Nat.dist v.val w.val

instance (v w : Fin 5) : Decidable (FiveLetterEdge v w) := inferInstanceAs (Decidable (3 ≤ Nat.dist v.val w.val))

def FiveLetterWalk (n : ℕ) (v : Fin 5) :=
  {f : Fin (n + 1) → Fin 5 // f 0 = v ∧
    ∀ i : Fin n, FiveLetterEdge (f i.castSucc) (f i.succ)}

noncomputable instance (n : ℕ) (v : Fin 5) : Fintype (FiveLetterWalk n v) := by
  classical
  unfold FiveLetterWalk
  infer_instance

private def fiveWalkZeroEquiv (v : Fin 5) : FiveLetterWalk 0 v ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨fun _ => v, rfl, fun i => Fin.elim0 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    fin_cases i
    exact f.property.1.symm
  right_inv u := by cases u; rfl

private def fiveWalkSplitEquiv (n : ℕ) (v : Fin 5) :
    FiveLetterWalk (n + 1) v ≃
      Σ w : {w : Fin 5 // FiveLetterEdge v w}, FiveLetterWalk n w.val where
  toFun f := ⟨⟨f.val 1, by
    have h := f.property.2 (0 : Fin (n + 1))
    change FiveLetterEdge (f.val 0) (f.val 1) at h
    rwa [f.property.1] at h⟩,
    ⟨Fin.tail f.val, rfl, fun i => f.property.2 i.succ⟩⟩
  invFun p := ⟨Fin.cons v p.2.val, by simp, by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change FiveLetterEdge v (p.2.val 0)
      rw [p.2.property.1]
      exact p.1.property
    · exact p.2.property.2 j⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact f.property.1.symm
    · rfl
  right_inv p := by
    rcases p with ⟨⟨w, hw⟩, f, hf, ha⟩
    change f 0 = w at hf
    subst w
    rfl

noncomputable def fiveLetterCount (n : ℕ) (v : Fin 5) : ℕ := Nat.card (FiveLetterWalk n v)

theorem five_letter_walk_count_zero (v : Fin 5) : fiveLetterCount 0 v = 1 := by
  unfold fiveLetterCount
  simpa using Nat.card_congr (fiveWalkZeroEquiv v)

theorem five_letter_walk_count_step (n : ℕ) (v : Fin 5) :
    fiveLetterCount (n + 1) v =
      ∑ w : Fin 5, if FiveLetterEdge v w then fiveLetterCount n w else 0 := by
  classical
  unfold fiveLetterCount
  rw [Nat.card_congr (fiveWalkSplitEquiv n v), Nat.card_sigma]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := FiveLetterEdge v)
    (Finset.univ.filter (FiveLetterEdge v)) (by simp)
    (fun w => Nat.card (FiveLetterWalk n w))).symm

theorem five_letter_walk_counts (n : ℕ) :
    fiveLetterCount n 0 = Nat.fib (n + 2) ∧
    fiveLetterCount n 1 = Nat.fib (n + 1) ∧
    fiveLetterCount n 3 = Nat.fib (n + 1) ∧
    fiveLetterCount n 4 = Nat.fib (n + 2) := by
  induction n with
  | zero => simp [five_letter_walk_count_zero, Nat.fib_add_two]
  | succ n ih =>
    rcases ih with ⟨h0, h1, h3, h4⟩
    simp only [five_letter_walk_count_step, Fin.sum_univ_succ]
    norm_num [FiveLetterEdge, Nat.dist, Fin.succ, h0, h1, h3, h4]
    change fiveLetterCount n 3 + fiveLetterCount n 4 = Nat.fib (n + 1 + 2) ∧
      fiveLetterCount n 4 = Nat.fib (n + 1 + 1) ∧
      Nat.fib (n + 2) + Nat.fib (n + 1) = Nat.fib (n + 1 + 2)
    rw [h3, h4]
    constructor
    · exact (Nat.fib_add_two (n := n + 1)).symm
    · exact ⟨rfl, (Nat.add_comm _ _).trans (Nat.fib_add_two (n := n + 1)).symm⟩

theorem five_letter_isolated_count (n : ℕ) : fiveLetterCount (n + 1) 2 = 0 := by
  rw [five_letter_walk_count_step]
  norm_num [Fin.sum_univ_succ, FiveLetterEdge, Nat.dist]

def FiveLetterWord (n : ℕ) :=
  {f : Fin n → Fin 5 // ∀ i j : Fin n, i.val + 1 = j.val → FiveLetterEdge (f i) (f j)}

noncomputable instance (n : ℕ) : Fintype (FiveLetterWord n) := by
  classical
  unfold FiveLetterWord
  infer_instance

private theorem fiveWordAdjacency (n : ℕ) (f : Fin (n + 1) → Fin 5) :
    (∀ i j : Fin (n + 1), i.val + 1 = j.val → FiveLetterEdge (f i) (f j)) ↔
      ∀ i : Fin n, FiveLetterEdge (f i.castSucc) (f i.succ) := by
  constructor
  · intro h i
    exact h i.castSucc i.succ rfl
  · intro h i j hij
    have hi : i.val < n := by have := j.isLt; omega
    let k : Fin n := ⟨i.val, hi⟩
    have hk0 : k.castSucc = i := Fin.ext rfl
    have hk1 : k.succ = j := Fin.ext hij
    simpa only [hk0, hk1] using h k

private def fiveWordSplitEquiv (n : ℕ) :
    FiveLetterWord (n + 1) ≃ Σ v : Fin 5, FiveLetterWalk n v where
  toFun f := ⟨f.val 0, ⟨f.val, rfl, (fiveWordAdjacency n f.val).mp f.property⟩⟩
  invFun p := ⟨p.2.val, (fiveWordAdjacency n p.2.val).mpr p.2.property.2⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨v, f, hf, ha⟩
    subst v
    rfl

private def fiveWordEmptyEquiv : FiveLetterWord 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  right_inv u := by cases u; rfl

theorem five_letter_word_count_succ (n : ℕ) :
    Nat.card (FiveLetterWord (n + 1)) =
      fiveLetterCount n 0 + fiveLetterCount n 1 + fiveLetterCount n 2 +
        fiveLetterCount n 3 + fiveLetterCount n 4 := by
  rw [Nat.card_congr (fiveWordSplitEquiv n), Nat.card_sigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change fiveLetterCount n 0 + (fiveLetterCount n 1 +
    (fiveLetterCount n 2 + (fiveLetterCount n 3 + fiveLetterCount n 4))) = _
  omega

theorem five_letter_word_count (n : ℕ) :
    Nat.card (FiveLetterWord n) =
      if n = 0 then 1 else if n = 1 then 5 else 2 * Nat.fib (n + 2) := by
  rcases n with _ | n
  · simpa using Nat.card_congr fiveWordEmptyEquiv
  rcases n with _ | n
  · rw [five_letter_word_count_succ]
    simp [five_letter_walk_count_zero]
  · rw [five_letter_word_count_succ]
    rcases five_letter_walk_counts (n + 1) with ⟨h0, h1, h3, h4⟩
    rw [h0, h1, h3, h4, five_letter_isolated_count]
    simp only [Nat.succ_ne_zero, if_false, Nat.succ.injEq]
    have h := Nat.fib_add_two (n := n + 2)
    change Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) at h
    change Nat.fib (n + 3) + Nat.fib (n + 2) + 0 +
      Nat.fib (n + 2) + Nat.fib (n + 3) = 2 * Nat.fib (n + 4)
    omega

def BoundedSeparatedWord (n : ℕ) :=
  {f : Fin n → ℕ // (∀ i, 1 ≤ f i ∧ f i ≤ 5) ∧
    ∀ i j : Fin n, i.val + 1 = j.val → 3 ≤ Nat.dist (f i) (f j)}

def boundedSeparatedWordEquiv (n : ℕ) : BoundedSeparatedWord n ≃ FiveLetterWord n where
  toFun f := ⟨fun i => ⟨f.val i - 1, by have := f.property.1 i; omega⟩, by
    intro i j hij
    have hi := f.property.1 i
    have hj := f.property.1 j
    have h := f.property.2 i j hij
    change 3 ≤ Nat.dist (f.val i - 1) (f.val j - 1)
    rw [← Nat.dist_add_add_right _ 1 _]
    simpa only [Nat.sub_add_cancel hi.1, Nat.sub_add_cancel hj.1] using h⟩
  invFun f := ⟨fun i => (f.val i).val + 1, by
    constructor
    · intro i
      have := (f.val i).isLt
      change 1 ≤ (f.val i).val + 1 ∧ (f.val i).val + 1 ≤ 5
      omega
    · intro i j hij
      rw [Nat.dist_add_add_right]
      exact f.property i j hij⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact Nat.sub_add_cancel (f.property.1 i).1
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp

instance (n : ℕ) : Finite (BoundedSeparatedWord n) :=
  Finite.of_equiv (FiveLetterWord n) (boundedSeparatedWordEquiv n).symm

theorem bounded_separated_word_count (n : ℕ) :
    Nat.card (BoundedSeparatedWord n) =
      if n = 0 then 1 else if n = 1 then 5 else 2 * Nat.fib (n + 2) := by
  rw [Nat.card_congr (boundedSeparatedWordEquiv n)]
  exact five_letter_word_count n

theorem solution (n : ℕ) :
    ∃ F : ℕ → ℕ, ∀ k : ℕ, k ≤ n - 1 → F (k + 1) - F k ≥ 3 := by
  refine ⟨fun k => 3 * k, ?_⟩
  intro k _
  change 3 * (k + 1) - 3 * k ≥ 3
  omega
