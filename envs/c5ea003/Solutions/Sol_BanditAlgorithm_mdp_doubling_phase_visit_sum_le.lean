-- Prove2me | solution 1 for BanditAlgorithm.mdp_doubling_phase_visit_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:43:08.696516+00:00
-- url     : https://prove2.me/submissions/ada03976-253b-4364-8202-2b74b2ff9cab

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The doubling-phase visit sum (L&S Exercise 38.22)

UCRL2 starts a new phase as soon as the visit count of the state-action pair
just played has doubled.  Writing `b k` for the number of visits to a fixed
pair *before* phase `k` and `c k` for the visits *during* phase `k`, the phase
rule guarantees `c k ≤ 1 ∨ b k`, and the quantity that appears in Step 3 of the
proof of Theorem 38.6 is `∑_{k<K} c k / √(1 ∨ b k) ≤ (√2 + 1) √(b K)`.

The continuous intuition is `∫₀^K f'(k)/√(f k) dk = 2√(f K) − 2√(f 0)`
(L&S Eq. 38.21); the discrete statement is Exercise 38.22.

The whole proof is one telescoping step: with `M = 1 ∨ b k`, both `b k` and the
increment `c k` are at most `M`, hence `√(b k + c k) + √(b k) ≤ (√2 + 1)√M`,
and multiplying by `√(b k + c k) − √(b k)` turns this into
`c k / √M ≤ (√2 + 1)(√(b (k+1)) − √(b k))`.
-/

/-- One phase of the doubling schedule: if the current value `x` and the
increment `y` are both at most `M ≥ 1`, then `y/√M` is at most `√2 + 1` times
the increment of `√·`.  This is the discrete form of `∫ f'/√f = 2√f`. -/
theorem sqrt_increment_step {x y M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hM : 1 ≤ M)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    y / Real.sqrt M ≤ (Real.sqrt 2 + 1) * (Real.sqrt (x + y) - Real.sqrt x) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  set s := Real.sqrt (x + y) with hs
  set t := Real.sqrt x with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x + y := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = x := Real.sq_sqrt hx
  have hst : t ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hsle : s ≤ Real.sqrt 2 * Real.sqrt M := by
    rw [hs, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have htle : t ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hsum : s + t ≤ (Real.sqrt 2 + 1) * Real.sqrt M := by nlinarith [hsle, htle]
  have hy_eq : y = (s - t) * (s + t) := by nlinarith [hs2, ht2]
  have hdiff : 0 ≤ s - t := by linarith
  rw [div_le_iff₀ hsM]
  calc y = (s - t) * (s + t) := hy_eq
    _ ≤ (s - t) * ((Real.sqrt 2 + 1) * Real.sqrt M) :=
        mul_le_mul_of_nonneg_left hsum hdiff
    _ = (Real.sqrt 2 + 1) * (s - t) * Real.sqrt M := by ring

theorem solution (b c : ℕ → ℝ) (hb0 : b 0 = 0)
    (hc : ∀ k, 0 ≤ c k) (hstep : ∀ k, b (k + 1) = b k + c k)
    (hdouble : ∀ k, c k ≤ max 1 (b k)) (K : ℕ) :
    ∑ k ∈ Finset.range K, c k / Real.sqrt (max 1 (b k))
      ≤ (Real.sqrt 2 + 1) * Real.sqrt (b K) := by
  have hbnn : ∀ k, 0 ≤ b k := by
    intro k
    induction k with
    | zero => rw [hb0]
    | succ n ih => rw [hstep n]; linarith [hc n]
  induction K with
  | zero => simp [hb0]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hstepK : c K / Real.sqrt (max 1 (b K))
          ≤ (Real.sqrt 2 + 1) * (Real.sqrt (b K + c K) - Real.sqrt (b K)) :=
        sqrt_increment_step (hbnn K) (hc K) (le_max_left _ _)
          (le_max_right _ _) (hdouble K)
      have hbK := hstep K
      calc (∑ k ∈ Finset.range K, c k / Real.sqrt (max 1 (b k)))
            + c K / Real.sqrt (max 1 (b K))
          ≤ (Real.sqrt 2 + 1) * Real.sqrt (b K)
            + (Real.sqrt 2 + 1) * (Real.sqrt (b K + c K) - Real.sqrt (b K)) :=
              add_le_add ih hstepK
        _ = (Real.sqrt 2 + 1) * Real.sqrt (b (K + 1)) := by rw [hbK]; ring
