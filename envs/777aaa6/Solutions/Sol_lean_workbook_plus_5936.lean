-- Prove2me | solution 1 for lean_workbook_plus_5936
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:52.722287+00:00
-- url     : https://prove2.me/submissions/7e4b8917-3049-42e0-8f34-a5d94b7c7e3b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable def rationalNormValue (x y : ℝ) : ℝ :=
  1 / (x ^ 2 + y ^ 2) + x ^ 2 / (1 + x ^ 2) + y ^ 2 / (1 + y ^ 2)

theorem rational_norm_gap_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    rationalNormValue x y - 1 =
      (1 + x ^ 2 * y ^ 2 * (1 + x ^ 2 + y ^ 2)) /
        ((x ^ 2 + y ^ 2) * (1 + x ^ 2) * (1 + y ^ 2)) := by
  have hs : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have ha : 1 + x ^ 2 ≠ 0 := by positivity
  have hb : 1 + y ^ 2 ≠ 0 := by positivity
  dsimp [rationalNormValue]
  field_simp
  ring

theorem rational_norm_strict_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 < rationalNormValue x y := by
  have hn : 0 < 1 + x ^ 2 * y ^ 2 * (1 + x ^ 2 + y ^ 2) := by positivity
  have hd : 0 < (x ^ 2 + y ^ 2) * (1 + x ^ 2) * (1 + y ^ 2) := by positivity
  have hp := div_pos hn hd
  rw [← rational_norm_gap_identity x y hx hy] at hp
  linarith

theorem rational_norm_reciprocal_family (x : ℝ) (hx : 0 < x) :
    rationalNormValue x (1 / x) = 1 + 1 / (x ^ 2 + (1 / x) ^ 2) := by
  have h1 : 1 + x ^ 2 ≠ 0 := by positivity
  have h2 : 1 + (1 / x) ^ 2 ≠ 0 := by positivity
  have h3 : x ^ 2 + (1 / x) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [rationalNormValue]
  field_simp
  ring

theorem rational_norm_epsilon_witness (ε : ℝ) (hε : 0 < ε) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ rationalNormValue x y < 1 + ε := by
  let x := 1 + 1 / ε
  have hx : 1 < x := by
    have hrec : 0 < 1 / ε := one_div_pos.mpr hε
    dsimp [x]
    linarith
  have hx0 : 0 < x := by linarith
  have hmul : ε * x = ε + 1 := by
    dsimp [x]
    field_simp
  have hs : 0 < x ^ 2 + (1 / x) ^ 2 := by positivity
  have hxx : x < x ^ 2 + (1 / x) ^ 2 := by nlinarith [sq_nonneg (1 / x)]
  have hprod : 1 < ε * (x ^ 2 + (1 / x) ^ 2) :=
    lt_trans (by linarith : 1 < ε * x) (mul_lt_mul_of_pos_left hxx hε)
  have hsmall : 1 / (x ^ 2 + (1 / x) ^ 2) < ε := (div_lt_iff₀ hs).2 hprod
  refine ⟨x, 1 / x, hx0, by positivity, ?_⟩
  rw [rational_norm_reciprocal_family x hx0]
  linarith

theorem rational_norm_no_minimizer (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ rationalNormValue u v < rationalNormValue x y := by
  have hgap := rational_norm_strict_bound x y hx hy
  obtain ⟨u, v, hu, hv, he⟩ :=
    rational_norm_epsilon_witness ((rationalNormValue x y - 1) / 2) (by linarith)
  exact ⟨u, v, hu, hv, by linarith⟩

theorem rational_norm_greatest_lower_bound :
    IsGLB {t : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ t = rationalNormValue x y} 1 := by
  constructor
  · rintro t ⟨x, y, hx, hy, rfl⟩
    exact (rational_norm_strict_bound x y hx hy).le
  · intro b hb
    by_contra h
    have hpos : 0 < b - 1 := by linarith
    obtain ⟨x, y, hx, hy, hv⟩ := rational_norm_epsilon_witness (b - 1) hpos
    have hlow := hb (show rationalNormValue x y ∈
      {t : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ t = rationalNormValue x y} from
        ⟨x, y, hx, hy, rfl⟩)
    linarith

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 ≤ 1 / (x ^ 2 + y ^ 2) + x ^ 2 / (1 + x ^ 2) + y ^ 2 / (1 + y ^ 2) :=
  (rational_norm_strict_bound x y hx hy).le

#print axioms solution
#print axioms rational_norm_gap_identity
#print axioms rational_norm_strict_bound
#print axioms rational_norm_reciprocal_family
#print axioms rational_norm_epsilon_witness
#print axioms rational_norm_no_minimizer
#print axioms rational_norm_greatest_lower_bound
