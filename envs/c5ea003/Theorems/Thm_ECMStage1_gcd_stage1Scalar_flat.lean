-- Prove2me | Theorems.Thm_ECMStage1_gcd_stage1Scalar_flat
-- name    : ECMStage1.gcd_stage1Scalar_flat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:32:08.300606+00:00
-- url     : https://prove2.me/theorems/d1a1f922-2d51-4931-a767-383fae918417
-- title:
--   No dose response.
-- statement:
--   **No dose response.**  If no prime power that divides `m` lies strictly between the
--   two bounds, the two bounds give exactly the same firing count.
--
--   ```lean
--   theorem ECMStage1.gcd_stage1Scalar_flat{m B B' : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) (hB' : B' ≠ 0)
--       (h : ∀ q ∈ m.primeFactors, ∀ j, 1 ≤ j → j ≤ m.factorization q →
--         (q ^ j ≤ B ↔ q ^ j ≤ B')) :
--       Nat.gcd m (stage1Scalar B) = Nat.gcd m (stage1Scalar B') := by sorry
--
--   /-! ## The exact jump at a prime of the schedule -/
--
--
--   /-! ## The computed staircase -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ECMStage1DoseResponse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ECMStage1DoseResponse.lean#L73

-- Thm stub generated from Shared/ECMStage1DoseResponse.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1OrderCompletion

/-!
# Dose response of the stage-1 bound: monotone, but a staircase that saturates

The experiments varied the smoothness bound `B1` as a fraction of a target and found
the success rates *flat* in that fraction — no dose response.  The three previous files
give the exact count `gcd(m, k(B))`; this file settles how that count depends on `B`.

* `gcd_stage1_factorization`: the exponent of a prime `r` in the firing count is
  `min(v_r(m), ⌊log_r B⌋)`, and `0` before `r` enters the schedule.  Everything below
  is read off from this one formula.
* `stage1Scalar_dvd_of_le`, `gcd_stage1Scalar_dvd_of_le`: raising the bound can only
  increase the firing count (monotonicity).
* `gcd_stage1Scalar_flat`: **no dose response.**  Raising the bound from `B` to `B'`
  changes nothing unless some prime power `q^j` that actually divides `m` lies in
  `(B, B']`.  Rates are therefore piecewise constant in the bound, with jumps only at
  the (few) prime powers dividing the order — exactly the flat-in-`B1frac` behaviour
  that was recorded.
* `gcd_stage1Scalar_eq_self_iff`: **saturation.**  The count reaches its maximum `m`
  precisely when `m` is `B`-powersmooth; beyond that, more dose buys nothing.
* `gcd_stage1_jump`: the exact multiplicative jump at a prime `q` of the schedule,
  `gcd(m,k(B,q)) = gcd(m,k(B,q-1)) · q^{min(v_q m, ⌊log_q B⌋)}`.
* `staircase_720_ten`: the whole staircase for `m = 720`, `B = 10`, computed:
  `1, 8, 72, 360, 360` at cutoffs `1, 2, 3, 5, 7`.  Two of the four schedule steps do
  nothing at all.
-/

open ECMStage1

open Finset

/-! ## Monotonicity in the bound -/




/-! ## No dose response between prime powers -/

theorem ECMStage1.gcd_stage1Scalar_flat{m B B' : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) (hB' : B' ≠ 0)
    (h : ∀ q ∈ m.primeFactors, ∀ j, 1 ≤ j → j ≤ m.factorization q →
      (q ^ j ≤ B ↔ q ^ j ≤ B')) :
    Nat.gcd m (stage1Scalar B) = Nat.gcd m (stage1Scalar B') := by sorry
