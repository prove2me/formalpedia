-- Prove2me | Definitions.Def_Novelty_BerggrenTreeSilverGrowth
-- name    : Novelty_BerggrenTreeSilverGrowth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:18:13.505439+00:00
-- url     : https://prove2.me/theorems/8608adc6-93ed-441e-87dd-b6b4eca289b0
-- title:
--   Aether Catalog definitions — Novelty_BerggrenTreeSilverGrowth
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BerggrenTreeSilverGrowth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BerggrenTreeSilverGrowth.lean by skeleton subtraction
import Mathlib
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

namespace BerggrenZeta

open Real

/-! ## Part A. The silver speed limit -/








/-! ## Part B. The three spines: one exponential, two quadratic -/

/-- The Pell (middle) spine: the word `MM…M` of length `k`. -/
def Mspine (k : ℕ) : List (Fin 3) := List.replicate k 1

/-- The left spine `LL…L` of length `k`. -/
def Lspine (k : ℕ) : List (Fin 3) := List.replicate k 0

/-- The right spine `RR…R` of length `k`. -/
def Rspine (k : ℕ) : List (Fin 3) := List.replicate k 2








/-! ## Part C. The depth slice of the tree zeta series -/


end BerggrenZeta


