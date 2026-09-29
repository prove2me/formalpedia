-- Prove2me | solution 1 for BerggrenZeta.hyp_step_le_silver
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:34:22.273327+00:00
-- url     : https://prove2.me/submissions/48a5b0dc-e5a3-47d8-8229-88ec44837279

-- Sol generated from Novelty/BerggrenTreeSilverGrowth.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore
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



/-- The quadratic form inequality behind the silver bound for the middle move. -/
theorem silver_quad_M (m n : ℝ) :
    5 * m ^ 2 + 4 * m * n + n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2))
      = ((2 * Real.sqrt 2 - 2) * m - 2 * n) ^ 2 := by
    linear_combination (4 * n ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]

/-- The quadratic form inequality behind the silver bound for the right move. -/
theorem silver_quad_R (m n : ℝ) :
    m ^ 2 + 4 * m * n + 5 * n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2))
      = (2 * m - (2 * Real.sqrt 2 - 2) * n) ^ 2 := by
    linear_combination (4 * m ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]




/-! ## Part B. The three spines: one exponential, two quadratic -/











/-! ## Part C. The depth slice of the tree zeta series -/



open BerggrenZeta in
theorem solution(i : Fin 3) (w : List (Fin 3)) :
    (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  have hs := sqrt_two_sq
  have hsq := one_le_sqrt_two
  set m : ℝ := ((seed w).1 : ℝ)
  set n : ℝ := ((seed w).2 : ℝ)
  fin_cases i
  · -- move `L`: `5m² - 4mn + n² ≤ 5 (m²+n²) ≤ (3+2√2)(m²+n²)`
    have hle : (seed w).2 ≤ 2 * (seed w).1 := by omega
    show ((hyp ((0 : Fin 3) :: w) : ℕ) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ)
    simp only [hyp, seed_cons, step, mvL]
    push_cast [hle]
    nlinarith
  · -- move `M`: the extremal (Pell) move
    simp only [hyp, seed_cons, step, mvM]
    push_cast
    have := silver_quad_M m n
    nlinarith
  · -- move `R`
    simp only [hyp, seed_cons, step, mvR]
    push_cast
    have := silver_quad_R m n
    nlinarith
