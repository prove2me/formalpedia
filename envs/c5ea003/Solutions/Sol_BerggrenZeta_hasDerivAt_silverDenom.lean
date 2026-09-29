-- Prove2me | solution 1 for BerggrenZeta.hasDerivAt_silverDenom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:40:33.22499+00:00
-- url     : https://prove2.me/submissions/72aef7c3-cf10-49dc-8c00-2ea18698a959

-- Sol generated from Novelty/BerggrenTreeSilverResidues.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverResidues
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
    HasDerivAt silverDenom
      (6 * (Real.log silverUnit : ℂ) * (silverUnit : ℂ) ^ (-2 * s)) s := by
  have hfun : silverDenom
      = fun z : ℂ => 1 - 3 * Complex.exp ((-2 * z) * (Real.log silverUnit : ℂ)) := by
    funext z
    rw [silverDenom, silver_cpow_eq_exp]
  have hlin : HasDerivAt (fun z : ℂ => (-2 * z) * (Real.log silverUnit : ℂ))
      (-2 * (Real.log silverUnit : ℂ)) s := by
    simpa using (((hasDerivAt_id s).const_mul (-2 : ℂ)).mul_const
      ((Real.log silverUnit : ℂ)))
  have hexp := hlin.cexp
  have hmul := (hexp.const_mul (3 : ℂ))
  have hsub := (hasDerivAt_const s (1 : ℂ)).sub hmul
  rw [hfun]
  convert hsub using 1
  rw [silver_cpow_eq_exp]
  ring
