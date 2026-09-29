-- Prove2me | Theorems.Thm_ScaleSmoothness_dial_eq_indicators
-- name    : ScaleSmoothness.dial_eq_indicators
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:48.973951+00:00
-- url     : https://prove2.me/theorems/4b43fa50-d1c0-4f4f-94c4-d8f006918927
-- title:
--   Pointwise decomposition of the dial into "is a nonzero residue" and "is zero".
-- statement:
--   Pointwise decomposition of the dial into "is a nonzero residue" and "is zero".
--
--   ```lean
--   theorem ScaleSmoothness.dial_eq_indicators(hp : p ≠ 2) (N : ZMod p) :
--       dial p N = 2 * (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuadraticDialIndependence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuadraticDialIndependence.lean#L68

-- Thm stub generated from NumberTheory/QuadraticDialIndependence.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion

/-!
# The dial vector of `x² − N` is exactly uniform: an independence theorem

`Catalog.NumberTheory.QRDialLocalStatistics` computed the moments of the QR dial
`dial p N = #{x | x² = N}` and
`Catalog.NumberTheory.ScaleSmoothnessDispersion` assembled them into the global
structure correction.  This file proves the *distributional* statement that
underlies the experimental design of round-73 #4 (exp 562): the vector of dials
`(dial p N)_{p ≤ B}` is **exactly uniform** on `{0,2}^k` as `N` ranges over the
residue data — the quadratic-residue pattern of `N` carries no bias whatsoever,
prime by prime *and jointly*.

## Main results

* `dial_eq_one_add_quadraticChar` — the bridge to Mathlib's quadratic character:
  `dial p N = 1 + χ_p(N)` as integers, valid for **all** `N`, including `N = 0`.
* `sum_quadraticChar_eq_zero` — an immediate consequence of the exact first
  moment `∑_N dial p N = p`: the quadratic character sums to zero.
* `two_mul_card_dial_two_add_one`, `two_mul_card_dial_zero_add_one` — exactly
  `(p−1)/2` residues are hit twice and `(p−1)/2` are missed.
* `card_dial_pattern` — **joint uniformity / independence**: for every prescribed
  pattern `d : ι → {0,2}` the number of residue data realising it is exactly
  `∏ (a i − 1) / 2^k`, independent of the pattern.
* `structureCorrection_max_value`, `card_structureCorrection_max` — the extreme
  values of the structure correction and the exact number of residue data
  attaining them.  Only a `2^{-k}` fraction of `N` sits at either extreme, which
  is why the observed clustering is `O(1)` and not exponential.
-/

open ScaleSmoothness

open Finset


variable (p : ℕ) [Fact p.Prime]

theorem ScaleSmoothness.dial_eq_indicators(hp : p ≠ 2) (N : ZMod p) :
    dial p N = 2 * (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0) := by sorry
