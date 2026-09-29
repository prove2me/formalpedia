-- Prove2me | Theorems.Thm_ScaleSmoothness_card_dial_pattern
-- name    : ScaleSmoothness.card_dial_pattern
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:59.32705+00:00
-- url     : https://prove2.me/theorems/7e60a0a0-557f-4217-bde0-2a4be7a32f64
-- title:
--   Exact independence of the QR dials.
-- statement:
--   **Exact independence of the QR dials.**  For every prescribed pattern
--   `d : ι → {0, 2}` of dials, the number of residue data realising it is the same,
--   namely `∏ (a i − 1) / 2^{#ι}`.  The quadratic-residue pattern of `N` is therefore
--   *exactly* uniform: there is no bias to exploit, at any smoothness bound.  This is
--   the arithmetic content of the histogram-matched control design.
--
--   ```lean
--   theorem ScaleSmoothness.card_dial_pattern(a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)
--       (d : ι → ℕ) (hd : ∀ i, d i = 0 ∨ d i = 2) :
--       2 ^ (Fintype.card ι) * #{N : (∀ i, ZMod (a i)) | ∀ i, dial (a i) (N i) = d i}
--         = ∏ i, (a i - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuadraticDialIndependence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuadraticDialIndependence.lean#L140

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







/-! ### Joint uniformity of the dial vector -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ScaleSmoothness.card_dial_pattern(a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)
    (d : ι → ℕ) (hd : ∀ i, d i = 0 ∨ d i = 2) :
    2 ^ (Fintype.card ι) * #{N : (∀ i, ZMod (a i)) | ∀ i, dial (a i) (N i) = d i}
      = ∏ i, (a i - 1) := by sorry
