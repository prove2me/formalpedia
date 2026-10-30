-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_nat_cube_mul_geometric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:51:08.752091+00:00
-- url     : https://prove2.me/submissions/d40cb9be-d389-41fd-b88d-406df53753e5

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: the cubic geometric sum (M₂-side ingredient)

`Σ'_{n} n³·yⁿ = y(1+4y+y²)/(1−y)⁴` — via
`n³ = 6·C(n+3,3) − 12·C(n+2,2) + 7·C(n+1,1) − C(n,0)`
(verified: n=1: 24−36+14−1=1 ✓, n=2: 60−72+21−1=8 ✓) over Mathlib's choose-geometric
sums; closed form check: `6 − 12(1−y) + 7(1−y)² − (1−y)³ = y(1+4y+y²)` ✓.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

end

set_option maxHeartbeats 800000
open Filter Finset
open scoped BigOperators Topology
theorem solution {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' n : ℕ, ((n : ℝ)) ^ 3 * y ^ n = y * (1 + 4 * y + y ^ 2) / (1 - y) ^ 4 := by
  have hy1 : (1 : ℝ) - y ≠ 0 := by
    intro h
    have : y = 1 := by linarith
    rw [this] at hy
    norm_num at hy
  have h0 : HasSum (fun n : ℕ => ((n + 0).choose 0 : ℝ) * y ^ n) (1 / (1 - y) ^ (0 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 0 hy
  have h1 : HasSum (fun n : ℕ => ((n + 1).choose 1 : ℝ) * y ^ n) (1 / (1 - y) ^ (1 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hy
  have h2 : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) * y ^ n) (1 / (1 - y) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hy
  have h3 : HasSum (fun n : ℕ => ((n + 3).choose 3 : ℝ) * y ^ n) (1 / (1 - y) ^ (3 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 3 hy
  have hcomb : HasSum (fun n : ℕ => ((n : ℝ)) ^ 3 * y ^ n)
      (6 * (1 / (1 - y) ^ 4) - 12 * (1 / (1 - y) ^ 3)
        + 7 * (1 / (1 - y) ^ 2) - 1 / (1 - y) ^ 1) := by
    have hstep := (((h3.mul_left 6).sub (h2.mul_left 12)).add (h1.mul_left 7)).sub h0
    convert hstep using 1
    funext n
    have hc3 : ((n + 3).choose 3 : ℝ)
        = ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1) / 6 := by
      have hnat : 6 * ((n + 3).choose 3) = (n + 3) * (n + 2) * (n + 1) := by
        have h1 : (n + 3).choose 3 = (n + 3).descFactorial 3 / Nat.factorial 3 :=
          Nat.choose_eq_descFactorial_div_factorial _ _
        have h3 : Nat.factorial 3 ∣ (n + 3).descFactorial 3 :=
          Nat.factorial_dvd_descFactorial _ _
        have h2 : (n + 3).descFactorial 3 = (n + 1) * ((n + 2) * (n + 3)) := by
          simp [Nat.descFactorial]
        have h6 : (6 : ℕ) = Nat.factorial 3 := by decide
        rw [h1, h6, Nat.mul_div_cancel' h3, h2]
        ring
      have hcast : (6 : ℝ) * ((n + 3).choose 3 : ℝ)
          = ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1) := by
        exact_mod_cast congrArg (fun z : ℕ => (z : ℝ)) hnat
      linarith
    have hc2 : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    have hc1 : ((n + 1).choose 1 : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.choose_one_right]
      push_cast
      ring
    have hc0 : ((n + 0).choose 0 : ℝ) = 1 := by
      rw [Nat.choose_zero_right]
      norm_num
    rw [hc3, hc2, hc1, hc0] at *
    ring
  rw [hcomb.tsum_eq]
  field_simp
  ring
