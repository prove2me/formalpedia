-- Prove2me | solution 1 for bousquet_phi_convexity_per_summand_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T02:29:37.77694+00:00
-- url     : https://prove2.me/submissions/c5c4a722-8b39-4ab5-a621-25d6166ea4b8

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

open Real

/-- **Bousquet 2002 eq(6) per-summand scalar core** (convexity of `φ(x)=e^x−x−1` through the
origin): for `0 ≤ y ≤ 1`,  `φ(−λ·y) ≤ y · φ(−λ)`, i.e.
`(e^{−λy} − (−λy) − 1) ≤ y·(e^{−λ} − (−λ) − 1)`. -/
theorem solution (lam y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (Real.exp (-(lam * y)) - (-(lam * y)) - 1)
      ≤ y * (Real.exp (-lam) - (-lam) - 1) := by
  set phi : ℝ → ℝ := fun x => Real.exp x - x - 1 with hphi
  have phi_zero : phi 0 = 0 := by simp [hphi]
  have hconv : ConvexOn ℝ Set.univ phi := by
    have he : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
    have haff : ConvexOn ℝ Set.univ (fun x : ℝ => -x - 1) := by
      have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => -x) := (concaveOn_id convex_univ).neg
      simpa using h1.add (convexOn_const (-1) convex_univ)
    have hpe : phi = Real.exp + (fun x : ℝ => -x - 1) := by
      funext x; simp only [hphi, Pi.add_apply]; ring
    rw [hpe]; exact he.add haff
  have key := hconv.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-lam))
    (by linarith : (0:ℝ) ≤ 1 - y) hy0 (by ring)
  simp only [smul_eq_mul, phi_zero, mul_zero, zero_add] at key
  have e1 : phi (y * -lam) = Real.exp (-(lam * y)) - (-(lam * y)) - 1 := by
    simp only [hphi]; ring_nf
  have e2 : phi (-lam) = Real.exp (-lam) - (-lam) - 1 := by simp only [hphi]
  rw [e1, e2] at key
  linarith [key]
