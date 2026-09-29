-- Prove2me | solution 1 for ECMStage1.gcd_stage1Scalar_flat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:47:50.192116+00:00
-- url     : https://prove2.me/submissions/740ecda0-930d-4bc7-b288-1f93d9645c69

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

/-- Key exponent identity: `min(v, ⌊log_q B⌋)` is the largest `j ≤ v` with `q^j ≤ B`. -/
theorem min_log_le_min_log {q v B B' : ℕ} (hq : q.Prime) (hB : B ≠ 0) (hB' : B' ≠ 0)
    (h : ∀ j, 1 ≤ j → j ≤ v → (q ^ j ≤ B ↔ q ^ j ≤ B')) :
    min v (Nat.log q B) ≤ min v (Nat.log q B') := by
  set j := min v (Nat.log q B) with hj
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · omega
  have hjv : j ≤ v := min_le_left _ _
  have hjlog : j ≤ Nat.log q B := min_le_right _ _
  have h1 : q ^ j ≤ B := (Nat.le_log_iff_pow_le hq.one_lt hB).mp hjlog
  have h2 : q ^ j ≤ B' := (h j hj0 hjv).mp h1
  have h3 : j ≤ Nat.log q B' := (Nat.le_log_iff_pow_le hq.one_lt hB').mpr h2
  exact le_min hjv h3



/-! ## The exact jump at a prime of the schedule -/


/-! ## The computed staircase -/




open ECMStage1 in
theorem solution{m B B' : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) (hB' : B' ≠ 0)
    (h : ∀ q ∈ m.primeFactors, ∀ j, 1 ≤ j → j ≤ m.factorization q →
      (q ^ j ≤ B ↔ q ^ j ≤ B')) :
    Nat.gcd m (stage1Scalar B) = Nat.gcd m (stage1Scalar B') := by
  refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm) ?_
  intro r
  by_cases hr : r.Prime
  · rw [stage1Scalar, stage1Scalar, gcd_stage1_factorization hm hr,
      gcd_stage1_factorization hm hr]
    by_cases hrm : r ∈ m.primeFactors
    · have hrpos : 0 < m.factorization r :=
        Nat.Prime.factorization_pos_of_dvd hr hm (Nat.dvd_of_mem_primeFactors hrm)
      have h1 : r ≤ B ↔ r ≤ B' := by
        have := h r hrm 1 le_rfl hrpos
        simpa using this
      by_cases hrB : r ≤ B
      · rw [if_pos hrB, if_pos (h1.mp hrB)]
        refine le_antisymm ?_ ?_
        · exact min_log_le_min_log hr hB hB' (h r hrm)
        · exact min_log_le_min_log hr hB' hB (fun j hj1 hj2 => (h r hrm j hj1 hj2).symm)
      · rw [if_neg hrB, if_neg (fun hc => hrB (h1.mpr hc))]
    · have hz : m.factorization r = 0 := by
        simp only [Nat.mem_primeFactors, not_and, not_not] at hrm
        exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hm (hrm hr hd))
      simp [hz]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
