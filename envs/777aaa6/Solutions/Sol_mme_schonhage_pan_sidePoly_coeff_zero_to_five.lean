-- Prove2me | solution 1 for mme_schonhage_pan_sidePoly_coeff_zero_to_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:06:11.815889+00:00
-- url     : https://prove2.me/submissions/36aedc00-390b-409e-b395-d02d1ac9628c

import Definitions.Def_mme_schonhage_pan_certificate

open BigOperators Finset Polynomial

universe u


namespace PanLowCoeffZeroToFive

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

open PanLeanBridge

private lemma coeff_mul_range (f g : K[X]) (n : ℕ) :
    (f * g).coeff n = ∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma coeff_zero (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 0 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma coeff_one (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 1 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma coeff_two (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 2 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma coeff_three (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 3 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma coeff_four (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 4 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial] <;>
    simp_rw [mul_assoc, ← Finset.mul_sum] <;>
    ring

private lemma coeff_five (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 5 = 0 := by
  simp [sidePoly, p3, p4, p5, p6, p7, p8, mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

end PanLowCoeffZeroToFive


theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (s : Fin 2)
    (n : ℕ) (hn : n < 6) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff n = 0 := by
  interval_cases n <;>
    simp only [PanLowCoeffZeroToFive.coeff_zero,
      PanLowCoeffZeroToFive.coeff_one, PanLowCoeffZeroToFive.coeff_two,
      PanLowCoeffZeroToFive.coeff_three, PanLowCoeffZeroToFive.coeff_four,
      PanLowCoeffZeroToFive.coeff_five]
