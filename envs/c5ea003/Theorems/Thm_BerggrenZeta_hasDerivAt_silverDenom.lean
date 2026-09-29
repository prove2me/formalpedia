-- Prove2me | Theorems.Thm_BerggrenZeta_hasDerivAt_silverDenom
-- name    : BerggrenZeta.hasDerivAt_silverDenom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:23:36.393002+00:00
-- url     : https://prove2.me/theorems/43d569ee-02f4-42c1-9d00-ec66732826d1
-- title:
--   The derivative of the denominator.
-- statement:
--   The derivative of the denominator.
--
--   ```lean
--   theorem BerggrenZeta.hasDerivAt_silverDenom(s : ℂ) :
--       HasDerivAt silverDenom
--         (6 * (Real.log silverUnit : ℂ) * (silverUnit : ℂ) ^ (-2 * s)) s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeSilverResidues.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeSilverResidues.lean#L58

-- Thm stub generated from Novelty/BerggrenTreeSilverResidues.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverResidues

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

theorem BerggrenZeta.hasDerivAt_silverDenom(s : ℂ) :
    HasDerivAt silverDenom
      (6 * (Real.log silverUnit : ℂ) * (silverUnit : ℂ) ^ (-2 * s)) s := by sorry
