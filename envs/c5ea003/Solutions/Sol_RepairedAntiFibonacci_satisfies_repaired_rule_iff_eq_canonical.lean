-- Prove2me | solution 1 for RepairedAntiFibonacci.satisfies_repaired_rule_iff_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:51.997987+00:00
-- url     : https://prove2.me/submissions/27ad9d14-45e7-42b7-98ea-647a6d8b5ea6

-- Sol generated from Logic/RepairedAntiFibonacciClassification.lean
import Mathlib
import Definitions.Def_Logic_RepairedAntiFibonacciClassification
import Theorems.Thm_RepairedAntiFibonacci_canonical_greedy_successor

/-!
# Classification of the repaired anti-Fibonacci process

The global additive repair from `Novelty.RepairedAntiFibonacci` is not merely
well-defined and increasing: its trajectory is forced exactly.  Starting from
one, the greedy process enumerates the positive odd integers.

The key point is that sums of earlier odd values are even.  At stage `n`, the
next odd value `2n+3` is therefore admissible, while the only smaller candidate
above `2n+1`, namely `2n+2`, is already the sum of the first and current values.
This gives both existence and uniqueness, and turns the earlier exponential
one-step ceiling into an exact linear law.
-/

open RepairedAntiFibonacci

noncomputable section





/-- Membership in the restricted sumset has the expected witness form. -/
lemma mem_priorPairSums_iff {a : ℕ → ℕ} {n s : ℕ} :
    s ∈ priorPairSums a n ↔ ∃ i < n, ∃ j < n, a i + a j = s := by
  simp only [priorPairSums, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, heq⟩
    exact ⟨i, hi, j, hj, heq⟩
  · rintro ⟨i, hi, j, hj, heq⟩
    exact ⟨⟨i, j⟩, ⟨hi, hj⟩, heq⟩


@[simp] theorem canonical_zero : canonical 0 = 1 := by
  norm_num [canonical]

/-- Restricted pair-sum sets depend only on the relevant finite prefix. -/
theorem priorPairSums_congr {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, a i = b i) :
    priorPairSums a n = priorPairSums b n := by
  classical
  ext s
  simp only [mem_priorPairSums_iff]
  constructor <;> rintro ⟨i, hi, j, hj, rfl⟩
  · exact ⟨i, hi, j, hj, by rw [h i hi, h j hj]⟩
  · exact ⟨i, hi, j, hj, by rw [← h i hi, ← h j hj]⟩

/-- Admissibility is invariant under replacement by an equal finite history. -/
theorem admissibleAfter_congr {a b : ℕ → ℕ} {n z : ℕ}
    (h : ∀ i ≤ n, a i = b i) :
    AdmissibleAfter a n z ↔ AdmissibleAfter b n z := by
  unfold AdmissibleAfter
  rw [h n (by omega), priorPairSums_congr (n := n + 1) (by
    intro i hi
    exact h i (by omega))]

/-- Greedy-successor status is invariant under replacement by an equal history. -/
theorem greedySuccessor_congr {a b : ℕ → ℕ} {n z : ℕ}
    (h : ∀ i ≤ n, a i = b i) :
    IsGreedySuccessor a n z ↔ IsGreedySuccessor b n z := by
  unfold IsGreedySuccessor
  simp only [admissibleAfter_congr h]

/-- A least admissible successor is unique. -/
theorem greedySuccessor_unique {a : ℕ → ℕ} {n x y : ℕ}
    (hx : IsGreedySuccessor a n x) (hy : IsGreedySuccessor a n y) : x = y := by
  exact Nat.le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)



/-- The positive odd integers satisfy the repaired global additive rule. -/
theorem canonical_satisfies_repaired_rule :
    SatisfiesRepairedRule canonical := by
  exact ⟨canonical_zero, canonical_greedy_successor⟩










open RepairedAntiFibonacci in
theorem solution(a : ℕ → ℕ) :
    SatisfiesRepairedRule a ↔ a = canonical := by
  constructor
  · intro ha
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact ha.1
      | succ n =>
        have hp : ∀ i ≤ n, a i = canonical i := by
          intro i hi
          exact ih i (by omega)
        have htrans : IsGreedySuccessor canonical n (a (n + 1)) :=
          (greedySuccessor_congr hp).mp (ha.2 n)
        exact greedySuccessor_unique htrans (canonical_greedy_successor n)
  · rintro rfl
    exact canonical_satisfies_repaired_rule
