-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_hash_collision_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:17:42.322556+00:00
-- url     : https://prove2.me/submissions/095033c3-4384-45f1-9718-0dd04225ebe0

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem fixed_hash_polynomial_le_exp
    (N : ℕ) :
    (((6 * (N + 1)) ^ 100 : ℕ) : ℝ) ≤
      Real.exp (800 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hx0 : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hx1 : 1 ≤ x := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    norm_num
  have hx2 : x ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp only [x]
    exact Real.sq_sqrt (by positivity)
  have h6 : (6 : ℝ) ≤ Real.exp 6 := by
    nlinarith [Real.add_one_le_exp (6 : ℝ)]
  have hxexp : x ≤ Real.exp x := by
    nlinarith [Real.add_one_le_exp x]
  have hxpow : x ^ 2 ≤ (Real.exp x) ^ 2 :=
    pow_le_pow_left₀ hx0.le hxexp 2
  have hexpSq : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  have hbase :
      (6 : ℝ) * x ^ 2 ≤ Real.exp (8 * x) := by
    calc
      (6 : ℝ) * x ^ 2 ≤ Real.exp 6 * (Real.exp x) ^ 2 := by
        exact mul_le_mul h6 hxpow (sq_nonneg x) (Real.exp_pos 6).le
      _ = Real.exp (6 + 2 * x) := by
        rw [hexpSq, ← Real.exp_add]
      _ ≤ Real.exp (8 * x) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  calc
    (((6 * (N + 1)) ^ 100 : ℕ) : ℝ) =
        ((6 : ℝ) * x ^ 2) ^ 100 := by
      push_cast
      rw [hx2]
      norm_num
    _ ≤ (Real.exp (8 * x)) ^ 100 :=
      pow_le_pow_left₀ (by positivity) hbase 100
    _ = Real.exp (800 * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf

private theorem fixed_hash_scaled_sqrt_le
    (N : ℕ) :
    Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ))) ≤
      32 * Real.sqrt ((((N + 1 : ℕ) : ℝ))) := by
  have hinside :
      (((1000 * N + 1 : ℕ) : ℝ)) ≤
        (1024 : ℝ) * (((N + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith
  calc
    Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ))) ≤
        Real.sqrt ((1024 : ℝ) * (((N + 1 : ℕ) : ℝ))) :=
      Real.sqrt_le_sqrt hinside
    _ = Real.sqrt (1024 : ℝ) *
        Real.sqrt ((((N + 1 : ℕ) : ℝ))) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    _ = 32 * Real.sqrt ((((N + 1 : ℕ) : ℝ))) := by
      have hsqrt : Real.sqrt (1024 : ℝ) = 32 := by
        rw [show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      rw [hsqrt]

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (N Dstar p Scard : ℕ)
    (hpScaled :
      (p : ℝ) ≤
        ((((6 * (N + 1)) ^ 100 * Dstar : ℕ) : ℝ)) *
          Real.exp
            (2000 *
              Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ)))))
    (hSsix :
      (6 * (((6 * (N + 1)) ^ 100 * Dstar) : ℕ) : ℝ) ≤
        (Scard : ℝ)) :
    let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
    (p : ℝ) ^ 2 *
          Real.exp
            (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))) +
        3 * (Dstar : ℝ) * (D : ℝ) ≤
      (Dstar : ℝ) * (Scard : ℝ) := by
  dsimp only
  let P : ℕ := (6 * (N + 1)) ^ 100
  let D : ℕ := P * Dstar
  let x : ℝ := Real.sqrt ((((N + 1 : ℕ) : ℝ)))
  have hpReal :
      (p : ℝ) ≤ (D : ℝ) * Real.exp (64000 * x) := by
    calc
      (p : ℝ) ≤
          (D : ℝ) *
            Real.exp
              (2000 *
                Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ)))) := by
        simpa only [D, P] using hpScaled
      _ ≤ (D : ℝ) * Real.exp (64000 * x) := by
        have hsqrt := fixed_hash_scaled_sqrt_le N
        have hexp :
            2000 * Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ))) ≤
              64000 * x := by
          nlinarith
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexp) (by positivity)
  have hPexp :
      (P : ℝ) ≤ Real.exp (800 * x) := by
    simpa only [P, x] using fixed_hash_polynomial_le_exp N
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hratio :
      (P : ℝ) * Real.exp (-872000 * x) ≤ 1 := by
    calc
      (P : ℝ) * Real.exp (-872000 * x) ≤
        Real.exp (800 * x) * Real.exp (-872000 * x) :=
          mul_le_mul_of_nonneg_right hPexp (Real.exp_pos _).le
      _ = Real.exp (-871200 * x) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith)
  have hpSq :
      (p : ℝ) ^ 2 ≤
        ((D : ℝ) * Real.exp (64000 * x)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hpReal
  have hpLoss :
      (p : ℝ) ^ 2 * Real.exp (-1000000 * x) ≤
        3 * (Dstar : ℝ) * (D : ℝ) := by
    calc
      (p : ℝ) ^ 2 * Real.exp (-1000000 * x) ≤
        ((D : ℝ) * Real.exp (64000 * x)) ^ 2 *
          Real.exp (-1000000 * x) :=
            mul_le_mul_of_nonneg_right hpSq (Real.exp_pos _).le
      _ = (D : ℝ) ^ 2 * Real.exp (-872000 * x) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ = (Dstar : ℝ) * (D : ℝ) *
          ((P : ℝ) * Real.exp (-872000 * x)) := by
        dsimp only [D]
        push_cast
        ring_nf
      _ ≤ (Dstar : ℝ) * (D : ℝ) * 1 := by
        gcongr
      _ ≤ 3 * (Dstar : ℝ) * (D : ℝ) := by
        have hnonneg : 0 ≤ (Dstar : ℝ) * (D : ℝ) := by positivity
        nlinarith
  have hscaled :
      (Dstar : ℝ) * (6 * (D : ℝ)) ≤
        (Dstar : ℝ) * (Scard : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    · simpa only [D, P] using hSsix
    · positivity
  dsimp only [x] at hpLoss
  calc
    (p : ℝ) ^ 2 *
          Real.exp
            (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))) +
        3 * (Dstar : ℝ) *
          ((((6 * (N + 1)) ^ 100 * Dstar : ℕ) : ℝ)) ≤
      3 * (Dstar : ℝ) * (D : ℝ) +
        3 * (Dstar : ℝ) * (D : ℝ) := by
      dsimp only [D, P] at hpLoss
      exact add_le_add_left hpLoss _
    _ = (Dstar : ℝ) * (6 * (D : ℝ)) := by ring_nf
    _ ≤ (Dstar : ℝ) * (Scard : ℝ) := hscaled
