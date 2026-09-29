-- Prove2me | solution 1 for ns_markov_grid_lemma
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T03:57:05.351786+00:00
-- url     : https://prove2.me/submissions/a950aca1-290a-410b-8e6d-e84d8fbe980b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ns_markov_grid_lemma
import Theorems.Thm_classical_markov_range
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Polynomial Set

namespace NSMarkovSketch

/-- Mean-value inequality for a polynomial on an interval:
if `|Q'(z)| ≤ B` on `[a,b]` and `x, y ∈ [a,b]`, then `|Q(x) - Q(y)| ≤ B·|x - y|`. -/
lemma mvt_dist_bound (Q : Polynomial ℝ) {a b : ℝ}
    (B : ℝ) (hB : ∀ z : ℝ, a ≤ z → z ≤ b → |Q.derivative.eval z| ≤ B)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |Q.eval x - Q.eval y| ≤ B * |x - y| := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun z => Q.eval z) (fun z => Q.derivative.eval z) hxy
      ((Polynomial.continuous Q).continuousOn)
      (fun z _ => Polynomial.hasDerivAt Q z)
    have hξa : a ≤ ξ := hx.1.trans hξmem.1.le
    have hξb : ξ ≤ b := hξmem.2.le.trans hy.2
    have hξB : |Q.derivative.eval ξ| ≤ B := hB ξ hξa hξb
    have hyx : (0 : ℝ) < y - x := by linarith
    have hne : (y : ℝ) - x ≠ 0 := by linarith
    have heq : Q.eval y - Q.eval x = Q.derivative.eval ξ * (y - x) := by
      have := hξ
      field_simp [hne] at this
      linarith [this]
    calc |Q.eval x - Q.eval y| = |Q.eval y - Q.eval x| := abs_sub_comm _ _
      _ = |Q.derivative.eval ξ| * |y - x| := by rw [heq, abs_mul]
      _ ≤ B * |y - x| := mul_le_mul_of_nonneg_right hξB (abs_nonneg _)
      _ = B * |x - y| := by rw [abs_sub_comm]
  · subst hxy; simp
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun z => Q.eval z) (fun z => Q.derivative.eval z) hxy
      ((Polynomial.continuous Q).continuousOn)
      (fun z _ => Polynomial.hasDerivAt Q z)
    have hξa : a ≤ ξ := hy.1.trans hξmem.1.le
    have hξb : ξ ≤ b := hξmem.2.le.trans hx.2
    have hξB : |Q.derivative.eval ξ| ≤ B := hB ξ hξa hξb
    have hxy' : (0 : ℝ) < x - y := by linarith
    have hne : (x : ℝ) - y ≠ 0 := by linarith
    have heq : Q.eval x - Q.eval y = Q.derivative.eval ξ * (x - y) := by
      have := hξ
      field_simp [hne] at this
      linarith [this]
    calc |Q.eval x - Q.eval y| = |Q.derivative.eval ξ| * |x - y| := by rw [heq, abs_mul]
      _ ≤ B * |x - y| := mul_le_mul_of_nonneg_right hξB (abs_nonneg _)

/-- `round` is monotone. -/
lemma round_mono' : Monotone (round : ℝ → ℤ) := by
  intro x y hxy
  rw [round_eq, round_eq]
  exact Int.floor_mono (by linarith)

/-- For `x ∈ [0, b]` (`b : ℕ`), there is an integer grid point `n ∈ {0, …, b}` within
distance `1/2` of `x`. -/
lemma exists_grid_near {b : ℕ} (x : ℝ) (hx0 : 0 ≤ x) (hxb : x ≤ (b : ℝ)) :
    ∃ n : ℕ, n ≤ b ∧ |x - (n : ℝ)| ≤ 1 / 2 := by
  have hr_nonneg : (0 : ℤ) ≤ round x := by
    have : round (0 : ℝ) ≤ round x := round_mono' hx0
    simpa using this
  have hr_le : round x ≤ (b : ℤ) := by
    have : round x ≤ round ((b : ℕ) : ℝ) := round_mono' hxb
    rw [round_natCast] at this
    exact this
  refine ⟨(round x).toNat, ?_, ?_⟩
  · exact Int.toNat_le.mpr hr_le
  · have hcast : (((round x).toNat : ℕ) : ℝ) = ((round x : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hr_nonneg
    rw [hcast]
    exact abs_sub_round x

end NSMarkovSketch

open NSMarkovSketch

theorem solution : ns_markov_grid_lemma := by
  intro b hb Q d h_deg h_lo h_hi h_d2b
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hbd2 : (0 : ℝ) < (b : ℝ) - (d : ℝ) ^ 2 := by linarith
  -- Extremum of Q on [0, b] via compactness.
  have hcompact : IsCompact (Set.Icc (0 : ℝ) (b : ℝ)) := isCompact_Icc
  have hnonempty : (Set.Icc (0 : ℝ) (b : ℝ)).Nonempty := ⟨0, ⟨le_refl 0, le_of_lt hb_pos⟩⟩
  have hcont : ContinuousOn (fun x => Q.eval x) (Set.Icc (0 : ℝ) (b : ℝ)) :=
    (Polynomial.continuous Q).continuousOn
  obtain ⟨xM, hxM_mem, hxM⟩ := hcompact.exists_isMaxOn hnonempty hcont
  obtain ⟨xm, hxm_mem, hxm⟩ := hcompact.exists_isMinOn hnonempty hcont
  set M := Q.eval xM with hMdef
  set m := Q.eval xm with hmdef
  have hmM : m ≤ M := by
    have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (b : ℝ) := ⟨le_refl 0, le_of_lt hb_pos⟩
    calc m ≤ Q.eval 0 := hxm hmem0
      _ ≤ M := hxM hmem0
  -- Apply the classical Markov child with the continuous range `[m, M]`.
  have hmarkov := classical_markov_range 0 (b : ℝ) hb_pos Q h_deg m M
    (fun x hx0 hxb => hxm ⟨hx0, hxb⟩) (fun x hx0 hxb => hxM ⟨hx0, hxb⟩)
  -- hmarkov : ∀ c, 0 ≤ c → c ≤ b → |Q'(c)| ≤ d²(M - m)/(b - 0) = d²(M - m)/b
  simp only [sub_zero] at hmarkov
  set B := (d : ℝ) ^ 2 * (M - m) / (b : ℝ) with hBdef
  have hBnonneg : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have : (0 : ℝ) ≤ M - m := by linarith
    positivity
  -- Nearest-grid bound for `M`: `M ≤ 1 + B/2`.
  have hMbound : M ≤ 1 + B / 2 := by
    obtain ⟨n, hn_le, hn_dist⟩ := exists_grid_near xM hxM_mem.1 hxM_mem.2
    have hQn_hi : Q.eval (n : ℝ) ≤ 1 := h_hi n hn_le
    have hdist : |Q.eval xM - Q.eval (n : ℝ)| ≤ B * (1 / 2) := by
      refine (mvt_dist_bound Q B hmarkov xM (n : ℝ) hxM_mem ?_).trans ?_
      · refine ⟨Nat.cast_nonneg n, ?_⟩
        exact_mod_cast hn_le
      · exact mul_le_mul_of_nonneg_left hn_dist hBnonneg
    have : Q.eval xM - Q.eval (n : ℝ) ≤ B * (1 / 2) := (le_abs_self _).trans hdist
    linarith
  -- Nearest-grid bound for `m`: `m ≥ -B/2`.
  have hmbound : -(B / 2) ≤ m := by
    obtain ⟨n, hn_le, hn_dist⟩ := exists_grid_near xm hxm_mem.1 hxm_mem.2
    have hQn_lo : (0 : ℝ) ≤ Q.eval (n : ℝ) := h_lo n hn_le
    have hdist : |Q.eval (n : ℝ) - Q.eval xm| ≤ B * (1 / 2) := by
      refine (mvt_dist_bound Q B hmarkov (n : ℝ) xm ?_ hxm_mem).trans ?_
      · refine ⟨Nat.cast_nonneg n, ?_⟩
        exact_mod_cast hn_le
      · rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hn_dist hBnonneg
    have : Q.eval (n : ℝ) - Q.eval xm ≤ B * (1 / 2) := (le_abs_self _).trans hdist
    linarith
  -- Combine: `M - m ≤ 1 + B`.
  have hrange : M - m ≤ 1 + B := by linarith
  -- Algebra: `B = d²(M-m)/b ≤ d²(1+B)/b`, so `B ≤ d²/(b - d²)`.
  have hBle : B ≤ (d : ℝ) ^ 2 / ((b : ℝ) - (d : ℝ) ^ 2) := by
    have hBb : B * (b : ℝ) = (d : ℝ) ^ 2 * (M - m) := by
      rw [hBdef]; field_simp
    have h1 : B * (b : ℝ) ≤ (d : ℝ) ^ 2 * (1 + B) := by
      rw [hBb]
      have hdnonneg : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
      nlinarith [hrange, hdnonneg]
    have h2 : B * ((b : ℝ) - (d : ℝ) ^ 2) ≤ (d : ℝ) ^ 2 := by nlinarith [h1]
    have hinv : (0 : ℝ) < ((b : ℝ) - (d : ℝ) ^ 2)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_right h2 (le_of_lt hinv)
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hbd2), mul_one, ← div_eq_mul_inv] at hm
  -- Conclude.
  intro c hc0 hcb
  exact (hmarkov c hc0 hcb).trans hBle
