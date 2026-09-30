-- Prove2me | solution 1 for lean_workbook_plus_60215
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:56:48.489965+00:00
-- url     : https://prove2.me/submissions/aa2c6f36-86b4-4175-8752-3c319c99982a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem cubic_recurrence_invariant (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) (n : ℕ) :
    -1 ≤ a n ∧ a n ≤ 0 := by
  induction n with
  | zero => rw [ha]; constructor <;> norm_num
  | succ n ih =>
    have hs : a n ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ a n + 1) (by linarith : 0 ≤ -a n)]
    constructor
    · apply (show Odd (3 : ℕ) by decide).pow_le_pow.mp
      nlinarith [hrec n, sq_nonneg (a n)]
    · apply (show Odd (3 : ℕ) by decide).pow_le_pow.mp
      nlinarith [hrec n]

theorem cubic_recurrence_negative_interval (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) (n : ℕ) :
    -1 ≤ a (n + 1) ∧ a (n + 1) ≤ -3 / 4 := by
  have hn := cubic_recurrence_invariant a ha hrec n
  refine ⟨(cubic_recurrence_invariant a ha hrec (n + 1)).1, ?_⟩
  have hs : a n ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ a n + 1) (by linarith : 0 ≤ -a n)]
  apply (show Odd (3 : ℕ) by decide).pow_le_pow.mp
  nlinarith [hrec n]

theorem cubic_recurrence_first (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) : a 1 = -1 := by
  apply (show Odd (3 : ℕ) by decide).pow_inj.mp
  have h := hrec 0
  rw [ha] at h
  nlinarith

theorem cubic_contraction_algebra (u v w : ℝ)
    (hu : -1 ≤ u ∧ u ≤ -3 / 4) (hv : -1 ≤ v ∧ v ≤ -3 / 4)
    (hw : -1 ≤ w ∧ w ≤ 0)
    (hc : u ^ 3 - v ^ 3 = (v ^ 2 - w ^ 2) / 2) :
    |u - v| ≤ (16 / 27 : ℝ) * |v - w| := by
  have huv : 9 / 16 ≤ u * v := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : u + 3 / 4 ≤ 0)
      (by linarith : v + 3 / 4 ≤ 0)]
  have hd : (27 / 16 : ℝ) ≤ u ^ 2 + u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + 3 / 4), sq_nonneg (v + 3 / 4)]
  have hvw : |v + w| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : (u - v) * (u ^ 2 + u * v + v ^ 2) = (v - w) * (v + w) / 2 := by
    nlinarith [hc]
  have habs := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ u ^ 2 + u * v + v ^ 2),
    abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  have hleft := mul_le_mul_of_nonneg_left hd (abs_nonneg (u - v))
  have hright := mul_le_mul_of_nonneg_left hvw (abs_nonneg (v - w))
  nlinarith

theorem cubic_recurrence_contraction (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) (n : ℕ) :
    |a (n + 2) - a (n + 1)| ≤ (16 / 27 : ℝ) * |a (n + 1) - a n| := by
  apply cubic_contraction_algebra
    (a (n + 2)) (a (n + 1)) (a n)
    (cubic_recurrence_negative_interval a ha hrec (n + 1))
    (cubic_recurrence_negative_interval a ha hrec n)
    (cubic_recurrence_invariant a ha hrec n)
  nlinarith [hrec n, hrec (n + 1)]

theorem cubic_recurrence_geometric_steps (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) (n : ℕ) :
    |a (n + 1) - a n| ≤ (16 / 27 : ℝ) ^ n := by
  induction n with
  | zero => rw [ha, cubic_recurrence_first a ha hrec]; norm_num
  | succ n ih =>
    calc
      |a (n + 2) - a (n + 1)| ≤ (16 / 27 : ℝ) * |a (n + 1) - a n| :=
        cubic_recurrence_contraction a ha hrec n
      _ ≤ (16 / 27 : ℝ) * (16 / 27 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (16 / 27 : ℝ) ^ (n + 1) := (pow_succ' _ _).symm

theorem cubic_recurrence_cauchy (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) : CauchySeq a := by
  apply cauchySeq_of_le_geometric (16 / 27 : ℝ) 1 (by norm_num)
  intro n
  simpa only [Real.dist_eq, abs_sub_comm, one_mul] using
    cubic_recurrence_geometric_steps a ha hrec n

theorem cubic_root_negative (x : ℝ) (hx : 2 * x ^ 3 - x ^ 2 + 2 = 0) : x < 0 := by
  by_contra hn
  have hp : 0 ≤ x := le_of_not_gt hn
  by_cases h : 1 / 2 ≤ x
  · nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 2 * x - 1)]
  · have hs : x ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hp (by linarith : 0 ≤ 1 / 2 - x)]
    nlinarith [mul_nonneg hp (sq_nonneg x)]

theorem cubic_root_unique (x y : ℝ)
    (hx : 2 * x ^ 3 - x ^ 2 + 2 = 0) (hy : 2 * y ^ 3 - y ^ 2 + 2 = 0) : x = y := by
  have hxn := cubic_root_negative x hx
  have hyn := cubic_root_negative y hy
  have hd : 0 < 2 * (x ^ 2 + x * y + y ^ 2) - (x + y) := by
    nlinarith [sq_nonneg (x + y / 2), sq_nonneg y]
  have he : (x - y) * (2 * (x ^ 2 + x * y + y ^ 2) - (x + y)) = 0 := by
    nlinarith [hx, hy]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hd))

theorem cubic_recurrence_limit (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) :
    ∃ L : ℝ, -1 ≤ L ∧ L ≤ -3 / 4 ∧ 2 * L ^ 3 - L ^ 2 + 2 = 0 ∧
      Tendsto a atTop (𝓝 L) ∧ ∀ n, |a n - L| ≤ (16 / 27 : ℝ) ^ n / (1 - 16 / 27) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cubic_recurrence_cauchy a ha hrec)
  have hs : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat 1).mpr hL
  have hlo : -1 ≤ L := ge_of_tendsto hs (Eventually.of_forall fun n =>
    (cubic_recurrence_negative_interval a ha hrec n).1)
  have hhi : L ≤ -3 / 4 := le_of_tendsto hs (Eventually.of_forall fun n =>
    (cubic_recurrence_negative_interval a ha hrec n).2)
  have hc : L ^ 3 = L ^ 2 / 2 - 1 := by
    apply tendsto_nhds_unique (hs.pow 3)
    have ht := ((hL.pow 2).div_const 2).sub_const 1
    simpa only [hrec] using ht
  refine ⟨L, hlo, hhi, by nlinarith, hL, ?_⟩
  intro n
  have hb : ∀ k, dist (a k) (a (k + 1)) ≤ 1 * (16 / 27 : ℝ) ^ k := by
    intro k
    simpa only [Real.dist_eq, abs_sub_comm, one_mul] using
      cubic_recurrence_geometric_steps a ha hrec k
  simpa only [Real.dist_eq, one_mul] using
    dist_le_of_le_geometric_of_tendsto (16 / 27 : ℝ) 1 (by norm_num) hb hL n

theorem source_cubic_recurrence_explicit_contraction (a : ℕ → ℝ) (ha : a 0 = 0)
    (hrec : ∀ n, a (n + 1) ^ 3 = a n ^ 2 / 2 - 1) :
    0 < (16 / 27 : ℝ) ∧ (16 / 27 : ℝ) < 1 ∧ ∀ n, 1 ≤ n →
      |a (n + 1) - a n| ≤ (16 / 27 : ℝ) * |a n - a (n - 1)| := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro n hn
  have h := cubic_recurrence_contraction a ha hrec (n - 1)
  rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] at h
  exact h

theorem posted_cubic_recurrence_constant_tail (a : ℕ → ℝ)
    (hrec : ∀ n, a (n + 1) = (1 / 2 * (a n)^2 - 1)^(1 / 3)) :
    ∀ n, a (n + 1) = 1 := by
  intro n
  simpa only [show 1 / 3 = (0 : ℕ) by decide, pow_zero] using hrec n

theorem solution (a : ℕ → ℝ) (ha : a 0 = 0)
    (ha_rec : ∀ n, a (n + 1) = (1 / 2 * (a n)^2 - 1)^(1 / 3)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ n, 1 ≤ n →
      abs (a (n + 1) - a n) ≤ q * abs (a n - a (n - 1)) := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro n hn
  have ht := posted_cubic_recurrence_constant_tail a ha_rec
  have he : n = (n - 1) + 1 := by omega
  have h : a n = 1 := he ▸ ht (n - 1)
  rw [ht n, h, sub_self, abs_zero]
  exact mul_nonneg (by norm_num) (abs_nonneg _)

#print axioms cubic_recurrence_invariant
#print axioms cubic_recurrence_negative_interval
#print axioms cubic_recurrence_first
#print axioms cubic_contraction_algebra
#print axioms cubic_recurrence_contraction
#print axioms cubic_recurrence_geometric_steps
#print axioms cubic_recurrence_cauchy
#print axioms cubic_root_negative
#print axioms cubic_root_unique
#print axioms cubic_recurrence_limit
#print axioms source_cubic_recurrence_explicit_contraction
#print axioms posted_cubic_recurrence_constant_tail
#print axioms solution
