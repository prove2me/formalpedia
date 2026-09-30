-- Prove2me | solution 1 for lean_workbook_plus_36113
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:49:29.48781+00:00
-- url     : https://prove2.me/submissions/f2caf47d-0b86-445a-b763-db16b47d6b60

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem integer_parameter_classification (d p : ℤ) (hd : 0 < d) (hp : 0 < p)
    (h : d * (d ^ 2 + 3 * p) = 100) :
    (d = 1 ∧ p = 33) ∨ (d = 4 ∧ p = 3) := by
  have hdp : 0 < d * p := mul_pos hd hp
  have hc : d ^ 3 < 100 := by nlinarith
  have hbound : d ≤ 4 := by
    by_contra hn
    have hd5 : 5 ≤ d := by omega
    have hd2 : 25 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 5)]
    have hm := mul_nonneg (show 0 ≤ d - 5 by omega) (show 0 ≤ d ^ 2 - 25 by omega)
    nlinarith
  interval_cases d <;> norm_num at h ⊢ <;> omega

theorem positive_pair_formula (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x = (Real.sqrt ((x - y) ^ 2 + 4 * (x * y)) + (x - y)) / 2 ∧
    y = (Real.sqrt ((x - y) ^ 2 + 4 * (x * y)) - (x - y)) / 2 := by
  have he : (x - y) ^ 2 + 4 * (x * y) = (x + y) ^ 2 := by ring
  rw [he, Real.sqrt_sq (by linarith : 0 ≤ x + y)]
  constructor <;> ring

theorem radical_pair_is_solution (d p : ℤ) (hd : 0 < d) (hp : 0 < p)
    (h : d * (d ^ 2 + 3 * p) = 100) :
    let x : ℝ := (Real.sqrt ((d : ℝ) ^ 2 + 4 * p) + d) / 2
    let y : ℝ := (Real.sqrt ((d : ℝ) ^ 2 + 4 * p) - d) / 2
    0 < x ∧ 0 < y ∧ x ^ 3 - y ^ 3 = 100 ∧
      (∃ k : ℤ, x - y = k) ∧ (∃ k : ℤ, x * y = k) := by
  intro x y
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hs := Real.sq_sqrt (show 0 ≤ (d : ℝ) ^ 2 + 4 * p by nlinarith [sq_nonneg (d : ℝ)])
  have hl : (d : ℝ) < Real.sqrt ((d : ℝ) ^ 2 + 4 * p) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hdiff : x - y = (d : ℝ) := by dsimp [x, y]; ring
  have hprod : x * y = (p : ℝ) := by dsimp [x, y]; nlinarith
  have hc : x ^ 3 - y ^ 3 = 100 := by
    calc
      _ = (x - y) * ((x - y) ^ 2 + 3 * (x * y)) := by ring
      _ = (d : ℝ) * ((d : ℝ) ^ 2 + 3 * p) := by rw [hdiff, hprod]
      _ = 100 := by exact_mod_cast h
  exact ⟨by dsimp [x]; linarith, by dsimp [y]; linarith, hc, ⟨d, hdiff⟩, ⟨p, hprod⟩⟩

theorem positive_solution_classification (x y : ℝ) :
    (0 < x ∧ 0 < y ∧ x ^ 3 - y ^ 3 = 100 ∧
      (∃ k : ℤ, x - y = k) ∧ (∃ k : ℤ, x * y = k)) ↔
    (x = (Real.sqrt 133 + 1) / 2 ∧ y = (Real.sqrt 133 - 1) / 2) ∨
    (x = (Real.sqrt 28 + 4) / 2 ∧ y = (Real.sqrt 28 - 4) / 2) := by
  constructor
  · rintro ⟨hx, hy, hc, ⟨d, hd⟩, ⟨p, hp⟩⟩
    have hpr : (0 : ℝ) < p := by rw [← hp]; exact mul_pos hx hy
    have hfactor : (d : ℝ) * ((d : ℝ) ^ 2 + 3 * p) = 100 := by
      rw [← hd, ← hp]
      nlinarith [hc]
    have hden : 0 < (d : ℝ) ^ 2 + 3 * p := by nlinarith [sq_nonneg (d : ℝ)]
    have hdr : (0 : ℝ) < d := by
      by_contra hn
      have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hden.le
      linarith
    have hd' : 0 < d := by exact_mod_cast hdr
    have hp' : 0 < p := by exact_mod_cast hpr
    have hf : d * (d ^ 2 + 3 * p) = 100 := by exact_mod_cast hfactor
    have hformula := positive_pair_formula x y hx hy
    rw [hd, hp] at hformula
    rcases integer_parameter_classification d p hd' hp' hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · norm_num at hformula
      exact Or.inl hformula
    · norm_num at hformula
      exact Or.inr hformula
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hm := radical_pair_is_solution 1 33 (by decide) (by decide) (by ring)
      norm_num at hm
      simpa using hm
    · have hm := radical_pair_is_solution 4 3 (by decide) (by decide) (by ring)
      norm_num at hm
      simpa using hm

theorem solution (x y : ℝ) (h₁ : x ^ 3 - y ^ 3 = 100)
    (h₂ : ∃ k : ℤ, x - y = k) (h₃ : ∃ k : ℤ, x * y = k) :
    ∃ x y : ℝ, x ^ 3 - y ^ 3 = 100 ∧ ∃ k : ℤ, x - y = k ∧ ∃ k : ℤ, x * y = k := by
  obtain ⟨d, hd⟩ := h₂
  exact ⟨x, y, h₁, d, hd, h₃⟩
