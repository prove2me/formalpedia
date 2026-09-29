-- Prove2me | solution 1 for BanditAlgorithm.arena_tuning_alpha
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T04:07:25.285407+00:00
-- url     : https://prove2.me/submissions/3910dd5d-db2c-4a99-8e4b-b20a6140eec8

import Mathlib.Data.Real.Sqrt

theorem solution
    (n k lam rho den N R : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hlam : 0 < lam) (hden : 0 < den) (hrho : 1 ≤ rho)
    (hR0 : 0 ≤ R) (hR2 : R ^ 2 = k * lam / (2 * (n + rho)))
    (hN0 : 0 ≤ N) (hNden : n - 14 * lam ≤ N * den)
    (hnr : n + rho ≤ 25 / 24 * n)
    (hg : 14 * lam + 1024 / 105 * den ≤ 4 / 25 * n)
    (hC : 300 * den ^ 2 ≤ n * k * lam) :
    6 / 5 * ((1 / 2 + 63 / 128 * (k - 1) * R / k) * rho)
      ≤ 3969 / 65536 * rho * N * R := by
  have hnr0 : (0 : ℝ) < n + rho := by linarith
  -- `B·den ≥ (3969/65536)·(21/25)·n`
  set B : ℝ := 3969 / 65536 * N - 189 / 320 with hB
  have hBden : 3969 / 65536 * (21 / 25 * n) ≤ B * den := by
    have h1 : 3969 / 65536 * (n - 14 * lam) ≤ 3969 / 65536 * (N * den) := by
      have : (0 : ℝ) ≤ 3969 / 65536 := by norm_num
      exact mul_le_mul_of_nonneg_left hNden this
    have h3 : 3969 / 65536 * (21 / 25 * n)
        ≤ 3969 / 65536 * (n - 14 * lam) - 189 / 320 * den := by
      have hin : (21 : ℝ) / 25 * n ≤ n - 14 * lam - 1024 / 105 * den := by linarith
      have h0 : (0 : ℝ) ≤ 3969 / 65536 := by norm_num
      have hmul := mul_le_mul_of_nonneg_left hin h0
      calc 3969 / 65536 * (21 / 25 * n)
          ≤ 3969 / 65536 * (n - 14 * lam - 1024 / 105 * den) := hmul
        _ = 3969 / 65536 * (n - 14 * lam) - 189 / 320 * den := by ring
    have h4 : 3969 / 65536 * (n - 14 * lam) - 189 / 320 * den ≤ B * den := by
      rw [hB]; nlinarith [h1]
    linarith
  have hBpos : 0 < B := by
    have : (0 : ℝ) < 3969 / 65536 * (21 / 25 * n) := by positivity
    nlinarith [hBden, hden]
  -- `25·k·λ·B² ≥ 18·(n+ρ)`
  have hsq : 18 * (n + rho) ≤ 25 * (k * lam) * B ^ 2 := by
    have hstep1 : 18 * (n + rho) * den ^ 2 ≤ 1 / 16 * (n ^ 2 * (k * lam)) := by
      have e1 : 18 * (n + rho) * den ^ 2 ≤ 18 * (25 / 24 * n) * den ^ 2 := by
        have : (0 : ℝ) ≤ den ^ 2 := sq_nonneg den
        nlinarith [hnr]
      have e2 : 18 * (25 / 24 * n) * den ^ 2 ≤ 75 / 4 * n * (n * k * lam / 300) := by
        have hd : den ^ 2 ≤ n * k * lam / 300 := by linarith
        nlinarith [hd, hn]
      have e3 : 75 / 4 * n * (n * k * lam / 300) = 1 / 16 * (n ^ 2 * (k * lam)) := by
        ring
      linarith
    have hstep2 : 25 * (k * lam) * (3969 / 65536 * (21 / 25 * n)) ^ 2
        ≤ 25 * (k * lam) * (B * den) ^ 2 := by
      have hpos : (0 : ℝ) ≤ 25 * (k * lam) := by positivity
      have h0 : (0 : ℝ) ≤ 3969 / 65536 * (21 / 25 * n) := by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hBden 2) hpos
    have hstep3 : 1 / 16 * (n ^ 2 * (k * lam))
        ≤ 25 * (k * lam) * (3969 / 65536 * (21 / 25 * n)) ^ 2 := by
      have hkl : (0 : ℝ) ≤ k * lam := by positivity
      nlinarith [sq_nonneg n, hkl, hn]
    have hcomb : 18 * (n + rho) * den ^ 2 ≤ 25 * (k * lam) * (B * den) ^ 2 := by
      linarith
    have hden2 : (0 : ℝ) < den ^ 2 := by positivity
    have : 18 * (n + rho) * den ^ 2 ≤ (25 * (k * lam) * B ^ 2) * den ^ 2 := by
      calc 18 * (n + rho) * den ^ 2 ≤ 25 * (k * lam) * (B * den) ^ 2 := hcomb
        _ = (25 * (k * lam) * B ^ 2) * den ^ 2 := by ring
    exact le_of_mul_le_mul_right (by linarith) hden2
  -- hence `R·B ≥ 3/5`
  have hRB : 3 / 5 ≤ R * B := by
    have hsq2 : (3 / 5 : ℝ) ^ 2 ≤ (R * B) ^ 2 := by
      have hR2' : R ^ 2 * (2 * (n + rho)) = k * lam := by
        rw [hR2]; field_simp
      have : (R * B) ^ 2 * (2 * (n + rho)) = (k * lam) * B ^ 2 := by
        rw [mul_pow, ← hR2']; ring
      nlinarith [hsq, hnr0, this]
    have hRBnn : 0 ≤ R * B := mul_nonneg hR0 hBpos.le
    nlinarith [hsq2, hRBnn]
  -- assemble
  have hΔle : 63 / 128 * (k - 1) * R / k ≤ 63 / 128 * R := by
    rw [div_le_iff₀ hk]
    nlinarith [hR0, hk]
  have hrho0 : (0 : ℝ) < rho := by linarith
  have hkey : 6 / 5 * (1 / 2 + 63 / 128 * R) ≤ 3969 / 65536 * N * R := by
    have : 3969 / 65536 * N * R = R * B + 189 / 320 * R := by rw [hB]; ring
    rw [this]
    linarith [hRB]
  calc 6 / 5 * ((1 / 2 + 63 / 128 * (k - 1) * R / k) * rho)
      ≤ 6 / 5 * ((1 / 2 + 63 / 128 * R) * rho) := by nlinarith [hΔle, hrho0]
    _ ≤ (3969 / 65536 * N * R) * rho := by nlinarith [hkey, hrho0]
    _ = 3969 / 65536 * rho * N * R := by ring
