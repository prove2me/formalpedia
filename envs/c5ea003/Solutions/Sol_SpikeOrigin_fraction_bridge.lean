-- Prove2me | solution 1 for SpikeOrigin.fraction_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:09:07.597635+00:00
-- url     : https://prove2.me/submissions/6f01de8c-8e27-43a6-9c63-88a29c2d10dc

import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy

open SpikeOrigin in
theorem solution {N : ℕ} (hlo : 2 ^ 95 ≤ N) :
    |((Nat.sqrt (N + 2 ^ 95 - 1) : ℝ) - (Nat.sqrt N : ℝ)) / (2 * (Nat.sqrt N : ℝ))
      - crossingPos (N : ℝ)| ≤ 3 / (Nat.sqrt N : ℝ) := by
  set a : ℝ := (Nat.sqrt (N + 2 ^ 95 - 1) : ℝ) with ha
  set s : ℝ := (Nat.sqrt N : ℝ) with hs
  set S : ℝ := Real.sqrt N with hSdef
  set A : ℝ := Real.sqrt ((N : ℝ) + 2 ^ 95) with hAdef
  have hNr : (2 : ℝ) ^ 95 ≤ N := by exact_mod_cast hlo
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  -- floors: `s ≤ S < s + 1` and `A - 2 < a ≤ A`
  have hs1 : (1 : ℝ) ≤ s := by
    have : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.2 (lt_of_lt_of_le (by positivity) hlo)
    show (1 : ℝ) ≤ (Nat.sqrt N : ℝ)
    exact_mod_cast this
  have hsS : s ≤ S := Real.nat_sqrt_le_real_sqrt
  have hSs : S < s + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hS0 : 0 < S := Real.sqrt_pos.2 hN0
  have hcast : ((N + 2 ^ 95 - 1 : ℕ) : ℝ) = (N : ℝ) + 2 ^ 95 - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have haA : a ≤ A := by
    have h1 : a ≤ Real.sqrt ((N + 2 ^ 95 - 1 : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    rw [hcast] at h1
    exact h1.trans (Real.sqrt_le_sqrt (by linarith))
  have hAa : A < a + 2 := by
    have h1 : Real.sqrt ((N + 2 ^ 95 - 1 : ℕ) : ℝ) < a + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    rw [hcast] at h1
    have h2 : A ≤ Real.sqrt ((N : ℝ) + 2 ^ 95 - 1) + 1 := by
      rw [hAdef, Real.sqrt_le_iff]
      have h3 := Real.sqrt_nonneg ((N : ℝ) + 2 ^ 95 - 1)
      have h4 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) + 2 ^ 95 - 1 by linarith)
      constructor
      · linarith
      · nlinarith
    linarith
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hAS : A ≤ 3 / 2 * S := by
    rw [hAdef, Real.sqrt_le_iff]
    have h4 := Real.sq_sqrt hN0.le
    constructor
    · positivity
    · rw [mul_pow, h4]
      linarith
  -- the unrounded quantity is exactly the crossing position
  have hcross : crossingPos (N : ℝ) = (A / S - 1) / 2 := by
    unfold crossingPos
    congr 2
    rw [hAdef, hSdef, ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have hs0 : 0 < s := by linarith
  have e : (a - s) / (2 * s) - (A / S - 1) / 2 = (a * S - A * s) / (2 * s * S) := by
    field_simp
    ring
  rw [hcross, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s * S),
    div_le_div_iff₀ (by positivity) hs0]
  -- `|aS - As| ≤ 6S`
  have hX : |a * S - A * s| ≤ 6 * S := by
    have e2 : a * S - A * s = (a - A) * S + A * (S - s) := by ring
    have h1 : -2 * S ≤ (a - A) * S := by nlinarith
    have h2 : 0 ≤ A * (S - s) := mul_nonneg hA0 (by linarith)
    have h3 : (a - A) * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0.le
    have h4 : A * (S - s) ≤ A := by nlinarith
    rw [abs_le, e2]
    constructor <;> linarith
  nlinarith
