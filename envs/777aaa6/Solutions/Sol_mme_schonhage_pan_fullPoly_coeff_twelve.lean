-- Prove2me | solution 1 for mme_schonhage_pan_fullPoly_coeff_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:02:12.500943+00:00
-- url     : https://prove2.me/submissions/88f6a8e7-1803-49df-8554-772e358f7e86

import Definitions.Def_mme_schonhage_pan_certificate

open BigOperators Finset Polynomial

universe u

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

noncomputable section

private lemma coeff_mul_range (f g : K[X]) (n : ℕ) :
    (f * g).coeff n = ∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma p3_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (PanLeanBridge.p3 (K := K) q0 q1 q2 s i k).coeff 12 =
      PanLeanBridge.ac q0 s i * PanLeanBridge.cc q1 s k i * PanLeanBridge.bc q2 s k +
      PanLeanBridge.uc q0 s k * PanLeanBridge.wc q1 s i * PanLeanBridge.vc q2 k i +
      PanLeanBridge.xc q0 s k i * PanLeanBridge.zc q1 k * PanLeanBridge.yc q2 s i := by
  simp [PanLeanBridge.p3, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]
  ring

private lemma p4_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) (i : Fin 5) :
    (PanLeanBridge.p4 (K := K) q0 q1 q2 s i).coeff 12 = 0 := by
  simp [PanLeanBridge.p4, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) (i : Fin 5) :
    (PanLeanBridge.p5 (K := K) q0 q1 q2 s i).coeff 12 = 0 := by
  simp [PanLeanBridge.p5, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) (k : Fin 11) :
    (PanLeanBridge.p6 (K := K) q0 q1 q2 s k).coeff 12 = 0 := by
  simp [PanLeanBridge.p6, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) :
    (PanLeanBridge.p7 (K := K) q0 q1 q2 s).coeff 12 = 0 := by
  simp [PanLeanBridge.p7, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) :
    (PanLeanBridge.p8 (K := K) q0 q1 q2 s).coeff 12 = 0 := by
  simp [PanLeanBridge.p8, PanLeanBridge.mon, coeff_mul_range,
    Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma sidePoly_coeff_twelve
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2)
    (s : Fin 2) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff 12 =
      PanLeanBridge.targetSide q0 q1 q2 s := by
  simp only [PanLeanBridge.sidePoly, PanLeanBridge.targetSide,
    Polynomial.coeff_add, Polynomial.finset_sum_coeff, p3_coeff_twelve,
    p4_coeff_twelve, p5_coeff_twelve, p6_coeff_twelve, p7_coeff_twelve,
    p8_coeff_twelve, Finset.sum_const_zero, add_zero]

theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1) (q2 : PanLeanBridge.Var2) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff 12 =
      ∑ s : Fin 2, PanLeanBridge.targetSide (K := K) q0 q1 q2 s := by
  simp [PanLeanBridge.fullPoly, sidePoly_coeff_twelve]

end
