-- Prove2me | solution 1 for BerggrenZeta.silverZeta_residue
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:55.587133+00:00
-- url     : https://prove2.me/submissions/87d8eabd-06b6-4b0a-a8bf-05c10d082211

-- Sol generated from Novelty/BerggrenTreeSilverResidues.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverResidues
import Theorems.Thm_BerggrenZeta_hasDerivAt_silverDenom
import Theorems.Thm_BerggrenZeta_log_silverUnit_pos

/-!
# Simple poles with a uniform residue: the explicit-formula constant of the Berggren tree

`Novelty.BerggrenTreeCriticalLine` locates the poles of the silver Ihara zeta
`Z(s) = (1 − 3ε^{-2s})^{-1}`, `ε = 1 + √2`, on the single vertical line `Re s = σ₀`.
This file completes the analytic picture of that critical line.

* `silverZeta_ne_zero` — `Z` has **no zeros** off its polar set: all of its critical
  structure is polar, so the "Riemann hypothesis" for this zeta is a statement about poles,
  not zeros;
* `silverZeta_period` — the exact functional equation `Z(s + iπ/log ε) = Z(s)`: the critical
  line is invariant under the translation by the pole spacing;
* `silverZeta_residue` — every pole is **simple** and all residues are equal to the same
  constant `1/(2 log ε)`, the analogue of the constant appearing in an explicit formula.
  Quantitatively `1/(2 log(1+√2)) = 0.5673…`.

The uniformity of the residues is the analytic shadow of the fact that the tree is exactly
`3`-regular at every depth, with every step scaling the silver length by exactly `ε²`.
-/

open BerggrenZeta

open Complex Filter Topology











open BerggrenZeta in
theorem solution{s₀ : ℂ} (h0 : silverDenom s₀ = 0) :
    Filter.Tendsto (fun s => (s - s₀) * silverZeta s) (𝓝[≠] s₀)
      (𝓝 (1 / (2 * (Real.log silverUnit : ℂ)))) := by
  have hL : 0 < Real.log silverUnit := log_silverUnit_pos
  have hLC : (Real.log silverUnit : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  -- at a pole, `ε^{-2s₀} = 1/3`, so the derivative of the denominator is `2 log ε`
  have hval : (silverUnit : ℂ) ^ (-2 * s₀) = 1 / 3 := by
    rw [silverDenom, sub_eq_zero] at h0
    linear_combination (-1 / 3 : ℂ) * h0
  have hderiv : HasDerivAt silverDenom (2 * (Real.log silverUnit : ℂ)) s₀ := by
    have := hasDerivAt_silverDenom s₀
    rw [hval] at this
    convert this using 1
    ring
  have hne : (2 : ℂ) * (Real.log silverUnit : ℂ) ≠ 0 := by
    simp [hLC]
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  have hinv := hderiv.inv₀ hne
  have heq : (fun s => (slope silverDenom s₀ s)⁻¹) =ᶠ[𝓝[≠] s₀]
      fun s => (s - s₀) * silverZeta s := by
    filter_upwards [self_mem_nhdsWithin] with s _
    rw [slope_def_field, h0, sub_zero, div_eq_mul_inv, mul_inv, inv_inv, silverZeta,
      ← silverDenom]
    ring
  simpa [one_div] using hinv.congr' heq
