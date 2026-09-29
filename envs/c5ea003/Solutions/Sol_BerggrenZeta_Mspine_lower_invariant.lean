-- Prove2me | solution 1 for BerggrenZeta.Mspine_lower_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:34:21.668507+00:00
-- url     : https://prove2.me/submissions/458e16a9-2878-4eb2-b53a-25490972f99c

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








/-! ## Part B. The three spines: one exponential, two quadratic -/








/-- The Pell spine obeys the silver recursion `m_{k+1} = 2 m_k + n_k`, `n_{k+1} = m_k`. -/
theorem Mspine_seed_succ (k : ℕ) :
    seed (Mspine (k + 1)) = (2 * (seed (Mspine k)).1 + (seed (Mspine k)).2,
      (seed (Mspine k)).1) := rfl



/-! ## Part C. The depth slice of the tree zeta series -/



open BerggrenZeta in
theorem solution(k : ℕ) :
    2 * (1 + Real.sqrt 2) ^ k ≤ ((seed (Mspine k)).1 : ℝ) ∧
      2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) ≤ ((seed (Mspine k)).2 : ℝ) := by
  have hs := sqrt_two_sq
  have h1 := one_le_sqrt_two
  have hsle : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  induction k with
  | zero =>
    constructor
    · norm_num [Mspine, seed]
    · norm_num [Mspine, seed]
      linarith
  | succ k ih =>
    obtain ⟨ihm, ihn⟩ := ih
    have hpow : (0 : ℝ) < (1 + Real.sqrt 2) ^ k := by positivity
    rw [Mspine_seed_succ]
    constructor
    · simp only
      push_cast
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) =
          2 * (2 * (1 + Real.sqrt 2) ^ k) + 2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) := by
        rw [pow_succ]
        ring
      rw [this]
      linarith
    · simp only
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) * (Real.sqrt 2 - 1) = 2 * (1 + Real.sqrt 2) ^ k := by
        rw [pow_succ]
        nlinarith
      rw [this]
      exact ihm
