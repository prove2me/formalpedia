-- Prove2me | solution 1 for TropPerron.wt_splice
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:22:57.374356+00:00
-- url     : https://prove2.me/submissions/9dd7433e-fede-400e-a22c-d6a421c2550c

-- Sol generated from Speculative/AutoResearch/TropicalPerronCore.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TropicalPerronCore

/-!
# Cuninghame-Green construction: the core of the tropical Perron-Frobenius theorem

This file supplies the combinatorial core needed to prove that every finite real
matrix has a max-plus eigenvector (`Speculative.AutoResearch.PerronTheorem`).

The classical construction is carried out here in an elementary, walk-based form:

* `wt M f k` is the weight of the length-`k` walk `f 0 → f 1 → ⋯ → f k`;
* `Wt hn M k i j` is the maximal weight of a length-`k` walk from `i` to `j`
  (defined by the tropical recursion `Wt (k+2) i j = max_l (M i l + Wt (k+1) l j)`);
* `wt_le_Wt` and `exists_wt_eq_Wt` identify `Wt` with the maximum over walks;
* `lam hn M` is the **maximal cycle mean** over closed walks of length at most `n`;
* `wt_splice` removes a closed sub-walk from a walk, and
  `Wt_sub_le_maxTo` (proved by strong induction, using the pigeonhole principle to
  locate a repeated vertex) shows that in the shifted matrix `M - lam` no walk beats
  the best walk of length at most `n`;
* `exists_eigen_potential` then produces the eigenvector: the potential
  `v i = max_{1 ≤ l ≤ n} (Wt l i i₀ - l * lam)`, taken relative to a critical node
  `i₀`, satisfies `max_j (M i j + v j) = lam + v i`.

Nothing here uses `sorry`, `native_decide`, or any new axiom.
-/

open Finset

open TropPerron

variable {n : ℕ}

/-! ### Walks and their weights -/








/-! ### Removing a closed sub-walk -/


/-! ### The maximal cycle mean -/





/-! ### The eigenvector -/



open TropPerron in
theorem solution(M : Matrix (Fin n) (Fin n) ℝ) (f : ℕ → Fin n) {a b k : ℕ}
    (hab : a < b) (hbk : b ≤ k) (heq : f a = f b) :
    wt M f k = wt M (fun t => if t < a then f t else f (t + (b - a))) (k - (b - a))
      + wt M (fun t => f (a + t)) (b - a) := by
  set d := b - a with hd
  have hbad : a + d = b := by omega
  set g : ℕ → Fin n := fun t => if t < a then f t else f (t + d) with hg
  have p2 : wt M (fun t => f (a + t)) d = ∑ t ∈ Finset.Ico a b, M (f t) (f (t + 1)) := by
    rw [wt, Finset.sum_Ico_eq_sum_range, ← hd]
    exact Finset.sum_congr rfl fun t _ => by rw [add_assoc]
  have p1a : ∑ t ∈ Finset.range a, M (g t) (g (t + 1))
      = ∑ t ∈ Finset.Ico 0 a, M (f t) (f (t + 1)) := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hta : t < a := (Finset.mem_Ico.mp ht).2
    have h1 : g t = f t := by simp [hg, hta]
    have h2 : g (t + 1) = f (t + 1) := by
      by_cases h : t + 1 < a
      · simp [hg, h]
      · have hte : t + 1 = a := by omega
        simp [hg, hte, hbad, heq]
    rw [h1, h2]
  have p1b : ∑ t ∈ Finset.Ico a (k - d), M (g t) (g (t + 1))
      = ∑ t ∈ Finset.Ico b k, M (f t) (f (t + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hlen : k - d - a = k - b := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : g (a + t) = f (a + t + d) := by
      simp only [hg]
      rw [if_neg (by omega)]
    have h2 : g (a + t + 1) = f (a + t + 1 + d) := by
      simp only [hg]
      rw [if_neg (by omega)]
    rw [h1, h2]
    congr 2 <;> omega
  have hsplit1 : ∑ t ∈ Finset.Ico 0 a, M (f t) (f (t + 1))
      + ∑ t ∈ Finset.Ico a b, M (f t) (f (t + 1))
      + ∑ t ∈ Finset.Ico b k, M (f t) (f (t + 1)) = wt M f k := by
    rw [wt, Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (by omega : 0 ≤ a) (by omega : a ≤ b)]
    rw [Finset.sum_Ico_consecutive _ (by omega : 0 ≤ b) hbk]
  have hgsplit : wt M g (k - d) = ∑ t ∈ Finset.range a, M (g t) (g (t + 1))
      + ∑ t ∈ Finset.Ico a (k - d), M (g t) (g (t + 1)) := by
    rw [wt, Finset.range_eq_Ico, Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ a) (by omega : a ≤ k - d)]
  rw [hgsplit, p1a, p1b, p2, ← hsplit1]
  ring
