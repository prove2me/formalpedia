-- Prove2me | solution 1 for BerggrenZeta.silverAbscissa_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:54.587741+00:00
-- url     : https://prove2.me/submissions/ecb07786-7660-46ba-9c37-678d89d4b7ed

-- Sol generated from Novelty/BerggrenTreeCriticalLine.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Theorems.Thm_BerggrenZeta_log_silverUnit_pos
import Theorems.Thm_BerggrenZeta_silverUnit_sq
import Theorems.Thm_BerggrenZeta_sqrt_two_sq

/-!
# A provable critical line: the silver Ihara zeta of the Berggren tree

The Berggren tree is a regular ternary tree whose extremal (Pell) branch grows at the rate
`ε² = 3 + 2√2`, where `ε = 1 + √2` is the fundamental unit of `ℤ[√2]` and the eigenvalue of
the hyperbolic Berggren generator (`Novelty.BerggrenTreeSilverGrowth`).  Weighting each of
the `3^k` nodes at depth `k` by the *silver length* `ε^{2k}` instead of by its actual
hypotenuse gives the **silver Ihara-type zeta function** of the tree,

`Z_ε(s) = ∑_{k ≥ 0} 3^k ε^{-2ks} = (1 - 3 ε^{-2s})⁻¹`.

Unlike the true tree zeta (whose abscissa is `1`, see `Novelty.BerggrenTreeZetaAbscissa`),
this object is *exactly solvable*: it is a rational function of `ε^{-2s}`, hence
meromorphic on all of `ℂ`, and its poles can be computed in closed form.  The result is a
rigorous analogue of the Riemann Hypothesis for the Berggren tree:

> **All poles of `Z_ε` lie on the single vertical line `Re s = σ₀`, where
> `σ₀ = log 3 / (2 log(1+√2))`, and on that line they form the arithmetic progression
> `s = σ₀ + i k π / log(1+√2)`, `k ∈ ℤ`.**

The "critical line" is therefore determined by exactly two pieces of tree geometry: the
branching number `3` and the silver growth exponent `2 log ε`; the spacing of the poles is
the reciprocal silver length `π / log ε`, the analogue of the Ihara/Selberg spectral gap.

## Main results

* `silverZeta_eq_tsum` — the Dirichlet series `∑ 3^k ε^{-2ks}` converges exactly on the
  half-plane `Re s > σ₀` and sums to `Z_ε`;
* `silver_denom_eq_zero_iff` — **the critical line theorem**: the pole set of `Z_ε` is
  `{s : Re s = σ₀, Im s ∈ (π / log ε) ℤ}`;
* `silverZeta_analyticAt` and `silverZeta_meromorphicOn` — meromorphic continuation to `ℂ`;
* `silverAbscissa_lt_one` — the silver critical abscissa is strictly smaller than the true
  abscissa `1` of the tree zeta function: the silver model *underestimates* the density of
  small hypotenuses, which is the precise reason the moonshot conjecture fails.
-/

open BerggrenZeta

open Real Complex








/-! ## Part A. The half-plane of convergence -/




/-! ## Part B. The critical line -/





/-! ## Part C. Meromorphic continuation -/




/-! ## Part D. The silver abscissa is strictly below the true abscissa -/




open BerggrenZeta in
theorem solution: silverAbscissa < 1 := by
  have hL : 0 < Real.log silverUnit := log_silverUnit_pos
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := sqrt_two_sq
    nlinarith [Real.sqrt_nonneg 2]
  have hlt : Real.log 3 < 2 * Real.log silverUnit := by
    have hpow : Real.log (silverUnit ^ 2) = 2 * Real.log silverUnit := by
      rw [Real.log_pow]
      norm_num
    rw [← hpow, silverUnit_sq]
    exact Real.log_lt_log (by norm_num) (by linarith)
  rw [silverAbscissa, div_lt_one (by positivity)]
  exact hlt
