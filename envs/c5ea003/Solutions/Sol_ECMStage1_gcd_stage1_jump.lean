-- Prove2me | solution 1 for ECMStage1.gcd_stage1_jump
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:47:51.461756+00:00
-- url     : https://prove2.me/submissions/8935612a-4209-4b91-ab3e-11b936d2cd06

-- Sol generated from Shared/ECMStage1DoseResponse.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_gcd_stage1_factorization

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




/-! ## The exact jump at a prime of the schedule -/


/-! ## The computed staircase -/




open ECMStage1 in
theorem solution{m B q : ℕ} (hm : m ≠ 0) (hq : q.Prime) :
    Nat.gcd m (stage1 B q)
      = Nat.gcd m (stage1 B (q - 1)) * q ^ min (m.factorization q) (Nat.log q B) := by
  have hq2 : 2 ≤ q := hq.two_le
  refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hm)
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hm) (pow_ne_zero _ hq.pos.ne')) ?_
  intro r
  by_cases hr : r.Prime
  · rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (pow_ne_zero _ hq.pos.ne'),
      Finsupp.add_apply, gcd_stage1_factorization hm hr, gcd_stage1_factorization hm hr,
      Nat.Prime.factorization_pow hq]
    rcases eq_or_ne r q with rfl | hrq
    · have h1 : ¬ r ≤ r - 1 := by omega
      simp [h1]
    · have h2 : (r ≤ q) ↔ (r ≤ q - 1) := by
        constructor
        · intro h
          have : r ≠ q := hrq
          omega
        · intro h; omega
      simp only [Finsupp.single_apply, if_neg (Ne.symm hrq), add_zero]
      by_cases hrq' : r ≤ q
      · rw [if_pos hrq', if_pos (h2.mp hrq')]
      · rw [if_neg hrq', if_neg (fun hc => hrq' (h2.mpr hc))]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
