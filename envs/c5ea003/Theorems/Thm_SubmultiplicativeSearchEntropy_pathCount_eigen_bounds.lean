-- Prove2me | Theorems.Thm_SubmultiplicativeSearchEntropy_pathCount_eigen_bounds
-- name    : SubmultiplicativeSearchEntropy.pathCount_eigen_bounds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:15:13.181854+00:00
-- url     : https://prove2.me/theorems/e286b112-5465-4ed0-9ec7-d4bf88fdf9ba
-- title:
--   Two-sided Perron estimate for path counts.
-- statement:
--   **Two-sided Perron estimate for path counts.** If `A` is nonnegative and has an eigenvector
--   `v` with `0 < c ≤ v i ≤ C` for the eigenvalue `r`, then the total number of length-`n` paths is
--   comparable to `r ^ n`, with constants depending only on `v`.
--
--   ```lean
--   theorem SubmultiplicativeSearchEntropy.pathCount_eigen_bounds(hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
--       (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v) (n : ℕ) :
--       c * pathCount A n ≤ r ^ n * (∑ i, v i) ∧ r ^ n * (∑ i, v i) ≤ C * pathCount A n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubmultiplicativeSearchEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubmultiplicativeSearchEntropy.lean#L174

-- Thm stub generated from Bridges/SubmultiplicativeSearchEntropy.lean
import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy

/-! # Submultiplicative search entropy and the Perron root

A bridge between three areas:

* **Combinatorics of proof search** — counting the successful prefixes of a search language;
* **Real analysis (Fekete's subadditive lemma)** — existence of the normalized logarithmic
  growth rate and its identification with the infimum of the finite-scale rates;
* **Linear algebra of nonnegative matrices (Perron theory)** — the growth rate of a
  finite-state pruned search equals `log ρ`, where `ρ` is the Perron eigenvalue of the
  automaton's transition matrix.
-/

open Filter Topology Set

open SubmultiplicativeSearchEntropy

/-! ## Part 1 — Submultiplicative counting functions and Fekete's lemma -/


open SearchProfile

variable (P : SearchProfile)

















/-! ## Part 2 — Nonnegative matrices: path counts of a finite-state pruning automaton -/


variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}





/-! ### Perron eigenvectors control path counts -/

variable {r : ℝ}

theorem SubmultiplicativeSearchEntropy.pathCount_eigen_bounds(hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
    (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v) (n : ℕ) :
    c * pathCount A n ≤ r ^ n * (∑ i, v i) ∧ r ^ n * (∑ i, v i) ≤ C * pathCount A n := by sorry
