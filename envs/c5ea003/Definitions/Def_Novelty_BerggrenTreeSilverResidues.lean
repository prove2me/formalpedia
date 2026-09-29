-- Prove2me | Definitions.Def_Novelty_BerggrenTreeSilverResidues
-- name    : Novelty_BerggrenTreeSilverResidues
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:20:27.680935+00:00
-- url     : https://prove2.me/theorems/3af90312-a024-4be8-93e6-0a87bc58f10b
-- title:
--   Aether Catalog definitions — Novelty_BerggrenTreeSilverResidues
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BerggrenTreeSilverResidues`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BerggrenTreeSilverResidues.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine

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

namespace BerggrenZeta

open Complex Filter Topology

/-- The denominator of the silver Ihara zeta. -/
noncomputable def silverDenom (s : ℂ) : ℂ := 1 - 3 * (silverUnit : ℂ) ^ (-2 * s)






/-- The `k`-th point of the critical line. -/
noncomputable def silverPole (k : ℤ) : ℂ :=
  (silverAbscissa : ℂ) + ((k * Real.pi / Real.log silverUnit : ℝ) : ℂ) * Complex.I



end BerggrenZeta


