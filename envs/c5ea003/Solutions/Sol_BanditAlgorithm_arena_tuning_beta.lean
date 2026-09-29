-- Prove2me | solution 1 for BanditAlgorithm.arena_tuning_beta
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T04:09:17.284155+00:00
-- url     : https://prove2.me/submissions/1caf6bf6-5acb-4159-8ccf-7663c68a578a

import Mathlib.Data.Real.Sqrt

theorem solution
    (n k lam rho den N R D SA : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hlam : 0 < lam) (hden : 0 < den) (hrho : 1 ≤ rho)
    (hD : 0 < D) (hSA : 0 < SA)
    (hR0 : 0 ≤ R) (hR2 : R ^ 2 = k * lam / (2 * (n + rho)))
    (hN0 : 0 ≤ N) (hNden : n - 14 * lam ≤ N * den)
    (hnr : n + rho ≤ 25 / 24 * n)
    (hg : 14 * lam + 1024 / 105 * den ≤ 4 / 25 * n)
    (hB : 2899 * (D * SA) * den ^ 2 ≤ 10 ^ 7 * rho ^ 2 * (k * lam)) :
    1 / 12500 * Real.sqrt (D * SA * n) ≤ 3969 / 65536 * rho * N * R / 6 := by
  have hnr0 : (0 : ℝ) < n + rho := by linarith
  have hrho0 : (0 : ℝ) < rho := by linarith
  set main : ℝ := 3969 / 65536 * rho * N * R with hmain
  -- `main·den ≥ (3969/65536)·ρ·(21/25)·n·R`
  have hNlow : 21 / 25 * n ≤ N * den := by linarith
  have hmainden : 3969 / 65536 * rho * (21 / 25 * n) * R ≤ main * den := by
    have h0 : (0 : ℝ) ≤ 3969 / 65536 * rho * R := by positivity
    have := mul_le_mul_of_nonneg_left hNlow h0
    calc 3969 / 65536 * rho * (21 / 25 * n) * R
        = 3969 / 65536 * rho * R * (21 / 25 * n) := by ring
      _ ≤ 3969 / 65536 * rho * R * (N * den) := this
      _ = main * den := by rw [hmain]; ring
  have hmain0 : 0 ≤ main := by
    rw [hmain]; positivity
  -- square the goal
  have hsq : D * SA * n ≤ (main / 6 * 12500) ^ 2 := by
    have hR2' : R ^ 2 * (2 * (n + rho)) = k * lam := by rw [hR2]; field_simp
    have hden2 : (0 : ℝ) < den ^ 2 := by positivity
    -- `(main·den)² ≥ (3969/65536)²ρ²(21/25)²n²R²`
    have h1 : (3969 / 65536 * rho * (21 / 25 * n) * R) ^ 2 ≤ (main * den) ^ 2 := by
      have h0 : (0 : ℝ) ≤ 3969 / 65536 * rho * (21 / 25 * n) * R := by positivity
      exact pow_le_pow_left₀ h0 hmainden 2
    -- eliminate `R²` and `(n+ρ)`
    have h2 : (3969 / 65536 * rho * (21 / 25 * n) * R) ^ 2 * (2 * (n + rho))
        = (3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 * (rho ^ 2 * (k * lam)) := by
      rw [show (3969 / 65536 * rho * (21 / 25 * n) * R) ^ 2
          = (3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 * rho ^ 2 * R ^ 2 by ring]
      rw [mul_assoc, hR2']
      ring
    have h3 : (2 : ℝ) * (n + rho) ≤ 25 / 12 * n := by linarith
    -- combine with `hB`
    have h4 : 2899 * (D * SA) * den ^ 2 * ((3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2)
        ≤ 10 ^ 7 * ((3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 * (rho ^ 2 * (k * lam))) := by
      have h0 : (0 : ℝ) ≤ (3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 := by positivity
      nlinarith [hB, h0]
    have h5 : (main * den) ^ 2 * (2 * (n + rho))
        ≥ (3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 * (rho ^ 2 * (k * lam)) := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt (by linarith : (0:ℝ) < 2 * (n + rho)))
      linarith [h2, this]
    have h6 : (main * den) ^ 2 * (25 / 12 * n)
        ≥ (3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2 * (rho ^ 2 * (k * lam)) := by
      have hmd : (0 : ℝ) ≤ (main * den) ^ 2 := sq_nonneg _
      nlinarith [h5, h3, hmd]
    -- now everything is polynomial
    have h7 : 2899 * (D * SA) * den ^ 2 * ((3969 / 65536) ^ 2 * (21 / 25) ^ 2 * n ^ 2)
        ≤ 10 ^ 7 * ((main * den) ^ 2 * (25 / 12 * n)) := by
      nlinarith [h4, h6]
    -- divide by `den²` and `n`
    have h8 : D * SA * n * den ^ 2 ≤ (main / 6 * 12500) ^ 2 * den ^ 2 := by
      nlinarith [h7, hn, hden2, sq_nonneg main]
    exact le_of_mul_le_mul_right (by linarith) hden2
  have hgoal : Real.sqrt (D * SA * n) ≤ main / 6 * 12500 := by
    have hpos : 0 ≤ main / 6 * 12500 := by positivity
    calc Real.sqrt (D * SA * n) ≤ Real.sqrt ((main / 6 * 12500) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = main / 6 * 12500 := Real.sqrt_sq hpos
  linarith [hgoal]
