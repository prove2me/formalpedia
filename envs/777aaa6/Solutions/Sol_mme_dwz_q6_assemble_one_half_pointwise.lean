-- Prove2me | solution 1 for mme_dwz_q6_assemble_one_half_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:21:15.179546+00:00
-- url     : https://prove2.me/submissions/ff0b56e1-4263-4da6-be6b-c3f87cc5e4c2

import Mathlib
import Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_extraction

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem exp_split_double_loss (C x : ℝ) :
    Real.exp (-(2 * C + 400) * x) =
      (Real.exp (-C * x)) ^ (2 : ℕ) *
        (Real.exp (-200 * x)) ^ (2 : ℕ) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem volume_weight_square
    (tau : ℝ) (volume : ℕ) :
    (((volume ^ 3 : ℕ) : ℝ) ^ tau) ^ (2 : ℕ) =
      (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
  let v : ℝ := ((volume ^ 3 : ℕ) : ℝ)
  have hv : 0 ≤ v := by positivity
  have hcast : (((((volume ^ 3) ^ 2 : ℕ) : ℝ))) = v ^ (2 : ℕ) := by
    dsimp only [v]
    norm_num
  rw [hcast]
  change (v ^ tau) ^ (2 : ℕ) = ((v ^ (2 : ℕ)) ^ tau)
  rw [pow_two, ← Real.mul_rpow hv hv, ← pow_two]

theorem solution
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (N L G A H : ℕ) (T : TensorObj K 3)
    (stars : CTensorOneHOneFamilyCertificate
      T A H (6 ^ (4 * G + 2 * L)))
    (hHbound : H ≤ 4 ^ N)
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (4 * N) *
          Real.exp (-(2 * C₀ + 400) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let volume : ℕ := 6 ^ (4 * G + 2 * L)
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hraw : 0 < raw := by
    dsimp only [raw]
    positivity
  have hH : 0 < H := by
    by_contra hn
    have hz : H = 0 := Nat.eq_zero_of_not_pos hn
    subst H
    have hleft :
        0 < (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
              (2 * N) *
            Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      positivity
    norm_num at hrate
    norm_num at hleft
    nlinarith
  obtain ⟨q, a, b, c, hrestrict, hextract⟩ :=
    mme_Ctensor_one_half_family_to_six_finite_extraction
      tau N A H volume (by simpa only [volume] using stars) hH hHbound
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  have hside : side = volume := by
    dsimp only [side, volume]
    rw [show (36 : ℕ) = 6 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hsideCube :
      (36 ^ (2 * G) * 6 ^ (2 * L)) *
          (36 ^ (2 * G) * 6 ^ (2 * L)) *
          (36 ^ (2 * G) * 6 ^ (2 * L)) = volume ^ 3 := by
    have h := hside
    dsimp only [side] at h
    rw [h]
    simp [pow_succ]
  let capacity : ℝ :=
    (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
      ((((volume ^ 3 : ℕ) : ℝ)) ^ tau)
  have hrate' : raw ^ (2 * N) * Real.exp (-C₀ * x) ≤ capacity := by
    rw [hsideCube] at hrate
    simpa only [raw, x, capacity] using hrate
  have hleft0 : 0 ≤ raw ^ (2 * N) * Real.exp (-C₀ * x) := by
    positivity
  have hsquared :
      (raw ^ (2 * N) * Real.exp (-C₀ * x)) ^ (2 : ℕ) ≤
        capacity ^ (2 : ℕ) :=
    pow_le_pow_left₀ hleft0 hrate' 2
  let sourceLoss : ℝ := Real.exp (-200 * x)
  let D : ℝ := (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2)
  let w : ℝ := ((((volume ^ 3 : ℕ) : ℝ)) ^ tau)
  have hweight : w ^ (2 : ℕ) =
      (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
    simpa only [w] using volume_weight_square tau volume
  change raw ^ (4 * N) * Real.exp (-(2 * C₀ + 400) * x) ≤ _
  calc
    raw ^ (4 * N) * Real.exp (-(2 * C₀ + 400) * x) =
        (raw ^ (2 * N) * Real.exp (-C₀ * x)) ^ (2 : ℕ) *
          sourceLoss ^ (2 : ℕ) := by
      rw [exp_split_double_loss]
      dsimp only [sourceLoss]
      have hrawpow : raw ^ (4 * N) =
          (raw ^ (2 * N)) ^ (2 : ℕ) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hrawpow, mul_pow]
      ring
    _ ≤ capacity ^ (2 : ℕ) * sourceLoss ^ (2 : ℕ) := by
      gcongr
    _ = (D * sourceLoss) ^ (2 : ℕ) *
          (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
      dsimp only [capacity, D, w]
      rw [← hweight]
      ring
    _ ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
      simpa only [D, sourceLoss, volume] using hextract
