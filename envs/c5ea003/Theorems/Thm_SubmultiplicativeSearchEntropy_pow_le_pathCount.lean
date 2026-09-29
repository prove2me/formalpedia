-- Prove2me | Theorems.Thm_SubmultiplicativeSearchEntropy_pow_le_pathCount
-- name    : SubmultiplicativeSearchEntropy.pow_le_pathCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:15:31.479987+00:00
-- url     : https://prove2.me/theorems/7e932696-f085-49d7-ac75-808453e2fdde
-- title:
--   Perron root is dominated by every finite path count.
-- statement:
--   **Perron root is dominated by every finite path count.**  A purely linear-algebraic
--   consequence of the entropy picture: submultiplicativity of path counts plus Fekete's lemma force
--   `r ^ n ≤ ∑ᵢⱼ (A ^ n)ᵢⱼ` for *every* `n`, for a nonnegative matrix with a positive eigenvector.
--
--   ```lean
--   theorem SubmultiplicativeSearchEntropy.pow_le_pathCount(hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j)
--       (h1 : ∀ n, 1 ≤ pathCount A n) {v : Fin k → ℝ} {c C : ℝ}
--       (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
--       (hr : 0 < r) (n : ℕ) :
--       r ^ n ≤ pathCount A n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubmultiplicativeSearchEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubmultiplicativeSearchEntropy.lean#L303

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

theorem SubmultiplicativeSearchEntropy.pow_le_pathCount(hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ n, 1 ≤ pathCount A n) {v : Fin k → ℝ} {c C : ℝ}
    (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
    (hr : 0 < r) (n : ℕ) :
    r ^ n ≤ pathCount A n := by sorry
