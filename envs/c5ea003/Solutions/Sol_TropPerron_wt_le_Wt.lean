-- Prove2me | solution 1 for TropPerron.wt_le_Wt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:22:56.875692+00:00
-- url     : https://prove2.me/submissions/01f2f6ed-2c85-4802-8c6f-1dab6d574865

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




lemma Wt_succ_succ (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    Wt hn M (k + 2) i j =
      Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun l => M i l + Wt hn M (k + 1) l j) := rfl

lemma wt_succ (M : Matrix (Fin n) (Fin n) ℝ) (f : ℕ → Fin n) (k : ℕ) :
    wt M f (k + 1) = M (f 0) (f 1) + wt M (fun t => f (t + 1)) k := by
  unfold wt
  rw [Finset.sum_range_succ']
  simp [add_comm]



/-! ### Removing a closed sub-walk -/


/-! ### The maximal cycle mean -/





/-! ### The eigenvector -/



open TropPerron in
theorem solution(hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ f : ℕ → Fin n, wt M f k ≤ Wt hn M k (f 0) (f k) := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro _ f
    match k, ih with
    | 0, _ => simp [wt, Wt]
    | (m + 1), ih =>
      rw [wt_succ, Wt_succ_succ]
      have h1 := ih (by omega) (fun t => f (t + 1))
      simp only at h1
      have h2 : M (f 0) (f 1) + wt M (fun t => f (t + 1)) (m + 1)
          ≤ M (f 0) (f 1) + Wt hn M (m + 1) (f 1) (f (m + 1 + 1)) := by linarith
      refine le_trans h2 ?_
      exact Finset.le_sup' (f := fun l => M (f 0) l + Wt hn M (m + 1) l (f (m + 1 + 1)))
        (Finset.mem_univ (f 1))
