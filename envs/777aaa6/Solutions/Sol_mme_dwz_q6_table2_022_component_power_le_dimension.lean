-- Prove2me | solution 1 for mme_dwz_q6_table2_022_component_power_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:59:29.887707+00:00
-- url     : https://prove2.me/submissions/addc9495-388c-4e59-83ea-ebf6ef07f4e2

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_q6_table2_022_profile_entropy_identity
import Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
import Theorems.Thm_mme_dwz_q6_table2_022_dimension_entropy_lower

open scoped BigOperators
open MME MME.DWZSquare MME.DWZTable2Component022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

theorem solution (tau : ℝ) (htau : 0 ≤ tau)
    (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    componentBase tau (9 : Fin 15) ^ m ≤
      ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau * (D : ℝ) ^ tau := by
  dsimp only
  let m := table2Power022 t
  let L := table2OuterCount022 t
  let G := table2MiddleCount022 t
  let D := Nat.card (Restricted022Word 6 m L G)
  let a : ℝ := splitA
  let g : ℝ := 1 - 2 * a
  let profile : Fin 3 → ℝ := ![a, g, a]
  let entropyFactor : ℝ :=
    Real.exp (Real.log 2 * mme_modern_entropyBits profile)
  let labelBase : ℝ := Real.rpow 6 (2 * g)
  let denom : ℝ := Real.rpow a (2 * a) * Real.rpow g g
  let Q : ℝ := labelBase / denom
  have hmpos : 0 < m := by
    dsimp [m, table2Power022]
    positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have ha : 0 < a := by
    dsimp [a]
    norm_num [splitA]
  have hg : 0 < g := by
    dsimp [g, a]
    norm_num [splitA]
  have hdenom : 0 < denom := by
    dsimp [denom]
    exact mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hg _)
  have hlabelBase : 0 < labelBase := by
    dsimp [labelBase]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hQ : 0 < Q := div_pos hlabelBase hdenom
  have hLratio : (L : ℝ) / (m : ℝ) = a := by
    dsimp only [L, m, a]
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    simp only [table2OuterCount022, table2Power022, Nat.cast_mul]
    dsimp only [splitA]
    field_simp [htR]
    ring
  have hGratio : (G : ℝ) / (m : ℝ) = g := by
    dsimp only [G, m, g, a]
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    simp only [table2MiddleCount022, table2Power022, Nat.cast_mul]
    dsimp only [splitA]
    field_simp [htR]
    ring
  have hbase : componentBase tau (9 : Fin 15) = Real.rpow Q tau := by
    have hinput :=
      mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
        (K := ℚ) tau t ht
    dsimp only at hinput
    have h := hinput.2.2.1
    rw [hLratio, hGratio] at h
    simpa only [Q, labelBase, denom, a, g] using h
  have hentropy : entropyFactor = 1 / denom := by
    have h := mme_dwz_q6_table2_022_profile_entropy_identity
    dsimp only at h
    simpa only [entropyFactor, profile, denom, a, g] using h
  have hlabel :
      labelBase ^ m = ((6 ^ (2 * G) : ℕ) : ℝ) := by
    have hexponent : (2 * g) * (m : ℝ) = ((2 * G : ℕ) : ℝ) := by
      rw [← hGratio]
      field_simp [ne_of_gt hmR]
      push_cast
      ring
    dsimp only [labelBase]
    rw [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 6)]
    rw [hexponent, Real.rpow_natCast]
    norm_cast
  have hQpow :
      Q ^ m =
        Real.exp ((m : ℝ) * Real.log 2 *
          mme_modern_entropyBits profile) *
          ((6 ^ (2 * G) : ℕ) : ℝ) := by
    have hEpow :
        Real.exp ((m : ℝ) * Real.log 2 *
            mme_modern_entropyBits profile) = entropyFactor ^ m := by
      dsimp only [entropyFactor]
      rw [show (m : ℝ) * Real.log 2 *
          mme_modern_entropyBits profile =
        (m : ℝ) * (Real.log 2 *
          mme_modern_entropyBits profile) by ring]
      rw [Real.exp_nat_mul]
    rw [hEpow, hentropy]
    dsimp only [Q]
    rw [div_pow, hlabel]
    rw [one_div, inv_pow]
    ring
  have hcomponentPower :
      componentBase tau (9 : Fin 15) ^ m =
        (Real.exp ((m : ℝ) * Real.log 2 *
            mme_modern_entropyBits profile) *
          ((6 ^ (2 * G) : ℕ) : ℝ)) ^ tau := by
    rw [hbase, Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hQ.le]
    rw [show tau * (m : ℝ) = (m : ℝ) * tau by ring]
    rw [Real.rpow_natCast_mul hQ.le]
    rw [hQpow]
  have hdim := mme_dwz_q6_table2_022_dimension_entropy_lower t ht
  dsimp only at hdim
  have hdim' :
      Real.exp ((m : ℝ) * Real.log 2 *
          mme_modern_entropyBits profile) *
          ((6 ^ (2 * G) : ℕ) : ℝ) ≤
        (6 * (((m + 1 : ℕ) : ℝ))) ^ 3 * (D : ℝ) := by
    simpa only [m, L, G, D, profile, a, g] using hdim
  rw [hcomponentPower]
  calc
    (Real.exp ((m : ℝ) * Real.log 2 *
          mme_modern_entropyBits profile) *
          ((6 ^ (2 * G) : ℕ) : ℝ)) ^ tau ≤
        ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3 * (D : ℝ)) ^ tau :=
      Real.rpow_le_rpow (by positivity) hdim' htau
    _ = ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau * (D : ℝ) ^ tau := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
