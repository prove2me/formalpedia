-- Prove2me | Theorems.Thm_BerggrenZeta_hyp_le_silver_pow
-- name    : BerggrenZeta.hyp_le_silver_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:22:46.618031+00:00
-- url     : https://prove2.me/theorems/0b0342ff-29ab-4975-9fc4-b9bd1f19bd1b
-- title:
--   The silver speed limit.
-- statement:
--   **The silver speed limit.**  At depth `k` no hypotenuse exceeds `5 (3+2√2)^k`.
--
--   ```lean
--   theorem BerggrenZeta.hyp_le_silver_pow(w : List (Fin 3)) :
--       (hyp w : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ w.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeSilverGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeSilverGrowth.lean#L99

-- Thm stub generated from Novelty/BerggrenTreeSilverGrowth.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# The silver growth dichotomy of the Berggren tree

The Berggren generators have spectral data governed by the units `3 ± 2√2 = (1 ± √2)²` of
`ℤ[√2]`.  This file makes the corresponding growth statements exact for the hypotenuse
`c(w) = m² + n²` of a node:

* `hyp_step_le_silver` — one Berggren move multiplies the hypotenuse by at most
  `3 + 2√2 = (1+√2)²`, the square of the silver ratio, for **all three** moves;
* `hyp_le_silver_pow` — hence `c(w) ≤ 5 · (3+2√2)^{|w|}`: the silver speed limit;
* `Mspine_hyp_lower`, `Mspine_silver_growth` — along the middle (Pell) spine the bound is
  attained up to a constant: `4 (3+2√2)^k ≤ c ≤ 5 (3+2√2)^k`;
* `Lspine_hyp`, `Rspine_hyp` — but along the two outer spines the hypotenuse grows only
  **quadratically**: `2k² + 6k + 5` and `4k² + 8k + 5`.

This dichotomy — exponential extremal branch, polynomial outer branches, `3^k` nodes at
depth `k` — is exactly what makes the abscissa of convergence of the tree zeta function
equal to `1` rather than the "silver" value `log 3 / (2 log(1+√2))` predicted by a purely
exponential branching model (see `Novelty.BerggrenTreeZetaAbscissa`).  The final result
`depth_slice_lower` quantifies the silver side: the depth-`k` slice of the tree zeta series
dominates the term `3^k (5 (3+2√2)^k)^{-s}` of the silver Ihara-type zeta of
`Novelty.BerggrenTreeCriticalLine`.
-/

open BerggrenZeta

-- open removed: section is not a namespace

/-! ## Part A. The silver speed limit -/

theorem BerggrenZeta.hyp_le_silver_pow(w : List (Fin 3)) :
    (hyp w : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ w.length := by sorry
