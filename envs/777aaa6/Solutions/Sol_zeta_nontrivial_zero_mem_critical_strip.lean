-- Prove2me | solution 1 for zeta_nontrivial_zero_mem_critical_strip
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T10:59:20.122452+00:00
-- url     : https://prove2.me/submissions/7ada4967-e9ed-4024-9b9e-c1891e7531eb

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex

/-- If `Re s ≤ 0` then `1 - s` is not a nonpositive integer. -/
private lemma one_sub_ne_neg_nat {s : ℂ} (hs : s.re ≤ 0) : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
  intro n hn
  have h : (1 - s).re = -(n : ℝ) := by rw [hn]; simp
  simp only [Complex.sub_re, Complex.one_re] at h
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem solution (s : ℂ) (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    push_neg at hle
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    set w : ℂ := 1 - s with hw
    have hwre : 1 ≤ w.re := by
      simp only [hw, Complex.sub_re, Complex.one_re]
      linarith
    have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := one_sub_ne_neg_nat hle
    have hw1 : w ≠ 1 := by
      intro h
      apply hs0
      have hs : s = 1 - w := by rw [hw]; ring
      rw [hs, h, sub_self]
    have hfe := riemannZeta_one_sub hwn hw1
    have hsw : (1 : ℂ) - w = s := by rw [hw]; ring
    rw [hsw, hz] at hfe
    have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      apply Complex.cpow_ne_zero_iff.mpr
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
    have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
    have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
      have hfe' := hfe.symm
      simp only [mul_eq_zero] at hfe'
      rcases hfe' with (((h | h) | h) | h) | h
      · exact absurd h (by norm_num)
      · exact absurd h h2pi
      · exact absurd h hGamma
      · exact h
      · exact absurd h hzw
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hwk : w = 2 * (k : ℂ) + 1 := by
      field_simp at hk
      linear_combination hk
    have hkre : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have hre : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
      linarith [hre ▸ hwre]
    have hk0 : 0 ≤ k := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (k : ℝ))
    have hsk : s = -2 * (k : ℂ) := by
      have hs : s = 1 - w := by rw [hw]; ring
      rw [hs, hwk]; ring
    have hk1 : 1 ≤ k := by
      rcases lt_or_eq_of_le hk0 with h | h
      · omega
      · exfalso; apply hs0; rw [hsk, ← h]; simp
    apply htriv
    refine ⟨(k - 1).toNat, ?_⟩
    have hcast : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
      have h : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) h
    rw [hcast, hsk]; ring
  · by_contra hge
    push_neg at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz
