-- Prove2me | Definitions.Def_Speculative_AutoResearch_TropicalPerronCore
-- name    : Speculative_AutoResearch_TropicalPerronCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:31:40.514176+00:00
-- url     : https://prove2.me/theorems/92e6db9d-4105-45d7-bc51-930f6246f035
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_TropicalPerronCore
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.TropicalPerronCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/TropicalPerronCore.lean by skeleton subtraction
import Mathlib

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

namespace TropPerron

variable {n : ℕ}

/-! ### Walks and their weights -/

/-- Weight of the length-`k` walk `f 0 → f 1 → ⋯ → f k`. -/
def wt (M : Matrix (Fin n) (Fin n) ℝ) (f : ℕ → Fin n) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range k, M (f t) (f (t + 1))

/-- Maximal weight of a length-`k` walk from `i` to `j`.  Only the values for `k ≥ 1`
are meaningful; `Wt _ _ 0` is set to `0`. -/
def Wt (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0, _, _ => 0
  | 1, i, j => M i j
  | (k + 2), i, j =>
      Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun l => M i l + Wt hn M (k + 1) l j)






/-! ### Removing a closed sub-walk -/


/-! ### The maximal cycle mean -/

/-- The index set `{1, …, n}` of admissible cycle lengths is nonempty. -/
lemma icc_nonempty (hn : 0 < n) : (Finset.Icc 1 n).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩⟩

/-- The maximal cycle mean: the largest mean weight of a closed walk of length at most
`n`. -/
noncomputable def lam (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (Finset.Icc 1 n).sup' (icc_nonempty hn)
    (fun k => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => Wt hn M k i i / k))



/-! ### The eigenvector -/


end TropPerron


