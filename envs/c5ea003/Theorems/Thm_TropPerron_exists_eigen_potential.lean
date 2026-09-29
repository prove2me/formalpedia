-- Prove2me | Theorems.Thm_TropPerron_exists_eigen_potential
-- name    : TropPerron.exists_eigen_potential
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:42.782978+00:00
-- url     : https://prove2.me/theorems/e058aa50-1974-4af5-8b91-76922fe8cdfd
-- title:
--   Cuninghame-Green.
-- statement:
--   **Cuninghame-Green.**  For every real square matrix there is a potential `v` with
--   `max_j (M i j + v j) = lam + v i` for all `i`.
--
--   ```lean
--   theorem TropPerron.exists_eigen_potential(hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
--       ∃ v : Fin n → ℝ, ∀ i : Fin n,
--         Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => M i j + v j)
--           = lam hn M + v i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/TropicalPerronCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/TropicalPerronCore.lean#L244

-- Thm stub generated from Speculative/AutoResearch/TropicalPerronCore.lean
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

theorem TropPerron.exists_eigen_potential(hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : Fin n → ℝ, ∀ i : Fin n,
      Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => M i j + v j)
        = lam hn M + v i := by sorry
