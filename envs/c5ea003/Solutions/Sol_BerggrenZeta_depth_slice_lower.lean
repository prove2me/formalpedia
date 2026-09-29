-- Prove2me | solution 1 for BerggrenZeta.depth_slice_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:39:02.503488+00:00
-- url     : https://prove2.me/submissions/aa4fd29c-55d4-438d-a1f9-c0a99aca3036

-- Sol generated from Novelty/BerggrenTreeSilverGrowth.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_hyp_le_silver_pow

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
theorem solution{s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (3 : ℝ) ^ k * (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤
      ∑ v : Fin k → Fin 3, (hyp (List.ofFn v) : ℝ) ^ (-s) := by
  have hterm : ∀ v : Fin k → Fin 3,
      (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤ (hyp (List.ofFn v) : ℝ) ^ (-s) := by
    intro v
    have hlen : (List.ofFn v).length = k := by simp
    have hle : (hyp (List.ofFn v) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
      have := hyp_le_silver_pow (List.ofFn v)
      rwa [hlen] at this
    have hpos : (0 : ℝ) < (hyp (List.ofFn v) : ℝ) := by
      have : 0 < hyp (List.ofFn v) := by
        obtain ⟨h1, h2, -, -⟩ := seed_isSeed (List.ofFn v)
        simp only [hyp]
        positivity
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hcard : (Finset.univ : Finset (Fin k → Fin 3)).card = 3 ^ k := by
    simp [Finset.card_univ]
  have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin k → Fin 3))
    (fun v => (hyp (List.ofFn v) : ℝ) ^ (-s)) _ (fun v _ => hterm v)
  rw [hcard, nsmul_eq_mul] at this
  simpa using this
