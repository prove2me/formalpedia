-- Prove2me | solution 1 for BerggrenZeta.silverZeta_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:55.078957+00:00
-- url     : https://prove2.me/submissions/055ac884-401b-49b6-b229-de570a6c7d9a

-- Sol generated from Novelty/BerggrenTreeSilverResidues.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverResidues
import Theorems.Thm_BerggrenZeta_log_silverUnit_pos
import Theorems.Thm_BerggrenZeta_silver_cpow_eq_exp

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
theorem solution(s : ℂ) :
    silverZeta (s + Complex.I * (Real.pi / Real.log silverUnit)) = silverZeta s := by
  have hL : 0 < Real.log silverUnit := log_silverUnit_pos
  have hLC : (Real.log silverUnit : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have key : (silverUnit : ℂ) ^ (-2 * (s + Complex.I * (Real.pi / Real.log silverUnit)))
      = (silverUnit : ℂ) ^ (-2 * s) := by
    rw [silver_cpow_eq_exp, silver_cpow_eq_exp]
    have hsplit : (-2 * (s + Complex.I * ((Real.pi : ℂ) / (Real.log silverUnit : ℂ))))
        * (Real.log silverUnit : ℂ)
        = (-2 * s) * (Real.log silverUnit : ℂ) + (-(2 * Real.pi)) * Complex.I := by
      field_simp
      ring
    push_cast at hsplit ⊢
    rw [hsplit, Complex.exp_add]
    have : Complex.exp ((-(2 * (Real.pi : ℂ))) * Complex.I) = 1 := by
      rw [show (-(2 * (Real.pi : ℂ))) * Complex.I = -(2 * Real.pi * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_two_pi_mul_I]
      norm_num
    rw [this, mul_one]
  simp only [silverZeta, key]
