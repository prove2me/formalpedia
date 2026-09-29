-- Prove2me | solution 1 for BerggrenZeta.Mspine_silver_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:37:23.648973+00:00
-- url     : https://prove2.me/submissions/01251def-7f4c-49ed-911f-78acfc82d356

-- Sol generated from Novelty/BerggrenTreeSilverGrowth.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_Mspine_lower_invariant
import Theorems.Thm_BerggrenZeta_hyp_le_silver_pow
import Theorems.Thm_BerggrenZeta_one_le_sqrt_two
import Theorems.Thm_BerggrenZeta_sqrt_two_sq

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

open Real

/-! ## Part A. The silver speed limit -/








/-! ## Part B. The three spines: one exponential, two quadratic -/











/-! ## Part C. The depth slice of the tree zeta series -/



open BerggrenZeta in
theorem solution(k : ℕ) :
    4 * (3 + 2 * Real.sqrt 2) ^ k ≤ (hyp (Mspine k) : ℝ) ∧
      (hyp (Mspine k) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
  have hs := sqrt_two_sq
  have h1 := one_le_sqrt_two
  constructor
  · obtain ⟨hm, -⟩ := Mspine_lower_invariant k
    have hsq : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by nlinarith
    have hpow : ((1 + Real.sqrt 2) ^ k) ^ 2 = (3 + 2 * Real.sqrt 2) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, hsq]
    have hmpos : (0 : ℝ) ≤ 2 * (1 + Real.sqrt 2) ^ k := by positivity
    have hcast : (hyp (Mspine k) : ℝ)
        = ((seed (Mspine k)).1 : ℝ) ^ 2 + ((seed (Mspine k)).2 : ℝ) ^ 2 := by
      simp only [hyp]
      push_cast
      ring
    rw [hcast]
    nlinarith [sq_nonneg ((seed (Mspine k)).2 : ℝ)]
  · have := hyp_le_silver_pow (Mspine k)
    simpa [Mspine, List.length_replicate] using this
