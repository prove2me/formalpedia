-- Prove2me | Theorems.Thm_SubmultiplicativeSearchEntropy_tendsto_pathCount_rate
-- name    : SubmultiplicativeSearchEntropy.tendsto_pathCount_rate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:15:14.322092+00:00
-- url     : https://prove2.me/theorems/f0e1825d-0b56-4ebf-9f4b-72872696aa7b
-- title:
--   Bridge theorem (linear algebra ↔ search entropy).
-- statement:
--   **Bridge theorem (linear algebra ↔ search entropy).**  For a nonnegative transition matrix
--   admitting a strictly positive eigenvector for the eigenvalue `r > 0` (the Perron situation of a
--   strongly connected pruning automaton), the normalized logarithmic growth rate of the number of
--   length-`n` accepted paths exists and equals `log r`.
--
--   ```lean
--   theorem SubmultiplicativeSearchEntropy.tendsto_pathCount_rate(hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
--       (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
--       (hr : 0 < r) :
--       Tendsto (fun n : ℕ => Real.log (pathCount A n) / n) atTop (𝓝 (Real.log r)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubmultiplicativeSearchEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubmultiplicativeSearchEntropy.lean#L244

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




/-! ## Part 3 — The growth rate of a Perron-controlled search equals `log r` -/



/-! ## Part 4 — The bridge theorem: Perron root = entropy = dimension -/


variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} {r : ℝ}

theorem SubmultiplicativeSearchEntropy.tendsto_pathCount_rate(hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
    (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => Real.log (pathCount A n) / n) atTop (𝓝 (Real.log r)) := by sorry
