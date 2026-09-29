-- Prove2me | solution 1 for mme_schonhage_pan_sidePoly_coeff_six_to_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:08:51.813506+00:00
-- url     : https://prove2.me/submissions/052f4658-bfe9-465d-8e8e-2837d3d09490

import Definitions.Def_mme_schonhage_pan_certificate

open BigOperators Finset Polynomial

universe u


namespace PanLowCoeffSixToNine

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

open PanLeanBridge

private lemma coeff_mul_range (f g : K[X]) (n : ℕ) :
    (f * g).coeff n = ∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma p3_six (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 6 =
      ac q0 s i * zc q1 k * yc q2 s i := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p4_six (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 6 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_six (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) :
    (p5 (K := K) q0 q1 q2 s i).coeff 6 =
      -(ac q0 s i * (∑ k : Fin 11, zc q1 k) * yc q2 s i) := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_six (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 6 =
      -((∑ i : Fin 5, ac q0 s i) * zc q1 k * (∑ i : Fin 5, yc q2 s i)) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_six (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 6 =
      (∑ i : Fin 5, ac q0 s i) * (∑ k : Fin 11, zc q1 k) *
        (∑ i : Fin 5, yc q2 s i) := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_six (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 6 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma side_six (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 6 = 0 := by
  simp only [sidePoly, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
    p3_six, p4_six, p5_six, p6_six, p7_six, p8_six,
    Finset.sum_const_zero, add_zero]
  have hmain : ((∑ i : Fin 5, ∑ k : Fin 11,
      ac q0 s i * zc q1 k * yc q2 s i) : K) =
      ((∑ i : Fin 5, ac q0 s i * (∑ k : Fin 11, zc q1 k) * yc q2 s i) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hlast :
      ((∑ k : Fin 11,
        -((∑ i : Fin 5, ac q0 s i) * zc q1 k *
          (∑ i : Fin 5, yc q2 s i))) : K) =
      (-((∑ i : Fin 5, ac q0 s i) * (∑ k : Fin 11, zc q1 k) *
        (∑ i : Fin 5, yc q2 s i)) : K) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hmain, hlast, Finset.sum_neg_distrib]
  ring

private lemma p3_seven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 7 =
      ac q0 s i * wc q1 s i * bc q2 s k := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p4_seven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 7 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_seven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) :
    (p5 (K := K) q0 q1 q2 s i).coeff 7 =
      -(ac q0 s i * wc q1 s i * (∑ k : Fin 11, bc q2 s k)) := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_seven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 7 =
      -((∑ i : Fin 5, ac q0 s i) * (∑ i : Fin 5, wc q1 s i) * bc q2 s k) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_seven (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 7 =
      (∑ i : Fin 5, ac q0 s i) * (∑ i : Fin 5, wc q1 s i) *
        (∑ k : Fin 11, bc q2 s k) := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_seven (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 7 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma side_seven (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 7 = 0 := by
  simp only [sidePoly, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
    p3_seven, p4_seven, p5_seven, p6_seven, p7_seven, p8_seven,
    Finset.sum_const_zero, add_zero]
  have hmain : ((∑ i : Fin 5, ∑ k : Fin 11,
      ac q0 s i * wc q1 s i * bc q2 s k) : K) =
      ((∑ i : Fin 5, ac q0 s i * wc q1 s i *
        (∑ k : Fin 11, bc q2 s k)) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]
  have hlast : ((∑ k : Fin 11,
      -((∑ i : Fin 5, ac q0 s i) * (∑ i : Fin 5, wc q1 s i) * bc q2 s k)) : K) =
      (-((∑ i : Fin 5, ac q0 s i) * (∑ i : Fin 5, wc q1 s i) *
        (∑ k : Fin 11, bc q2 s k)) : K) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.mul_sum]
  rw [hmain, hlast, Finset.sum_neg_distrib]
  ring

private lemma p3_eight (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 8 =
      ac q0 s i * wc q1 s i * vc q2 k i +
      uc q0 s k * wc q1 s i * yc q2 s i := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p4_eight (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 8 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_eight (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) :
    (p5 (K := K) q0 q1 q2 s i).coeff 8 =
      -(ac q0 s i * wc q1 s i * (∑ k : Fin 11, vc q2 k i) +
        (∑ k : Fin 11, uc q0 s k) * wc q1 s i * yc q2 s i) := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]
  ring

private lemma p6_eight (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 8 =
      -(uc q0 s k * (∑ i : Fin 5, wc q1 s i) * (∑ i : Fin 5, yc q2 s i)) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_eight (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 8 =
      (∑ k : Fin 11, uc q0 s k) * (∑ i : Fin 5, wc q1 s i) *
        (∑ i : Fin 5, yc q2 s i) := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_eight (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 8 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma side_eight (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 8 = 0 := by
  simp only [sidePoly, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
    p3_eight, p4_eight, p5_eight, p6_eight, p7_eight, p8_eight,
    Finset.sum_const_zero, add_zero]
  simp_rw [Finset.sum_add_distrib]
  have ha : ((∑ i : Fin 5, ∑ k : Fin 11,
      ac q0 s i * wc q1 s i * vc q2 k i) : K) =
      ((∑ i : Fin 5, ac q0 s i * wc q1 s i *
        (∑ k : Fin 11, vc q2 k i)) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]
  have hu : ((∑ i : Fin 5, ∑ k : Fin 11,
      uc q0 s k * wc q1 s i * yc q2 s i) : K) =
      ((∑ i : Fin 5, (∑ k : Fin 11, uc q0 s k) *
        wc q1 s i * yc q2 s i) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hlast :
      ((∑ k : Fin 11,
        -(uc q0 s k * (∑ i : Fin 5, wc q1 s i) *
          (∑ i : Fin 5, yc q2 s i))) : K) =
      (-((∑ k : Fin 11, uc q0 s k) * (∑ i : Fin 5, wc q1 s i) *
        (∑ i : Fin 5, yc q2 s i)) : K) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [ha, hu, hlast, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

private lemma p3_nine (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 9 =
      ac q0 s i * cc q1 s k i * yc q2 s i +
      ac q0 s i * zc q1 k * bc q2 s k := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]
  ring

private lemma p4_nine (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 9 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_nine (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) :
    (p5 (K := K) q0 q1 q2 s i).coeff 9 =
      -(ac q0 s i * (∑ k : Fin 11, cc q1 s k i) * yc q2 s i) := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_nine (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 9 =
      -((∑ i : Fin 5, ac q0 s i) * zc q1 k * bc q2 s k) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_nine (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 9 = 0 := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_nine (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 9 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma side_nine (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 9 = 0 := by
  simp only [sidePoly, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
    p3_nine, p4_nine, p5_nine, p6_nine, p7_nine, p8_nine,
    Finset.sum_const_zero, add_zero]
  simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hc : ((∑ i : Fin 5, ∑ k : Fin 11,
      ac q0 s i * cc q1 s k i * yc q2 s i) : K) =
      ((∑ i : Fin 5, ac q0 s i * (∑ k : Fin 11, cc q1 s k i) *
        yc q2 s i) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hz : ((∑ i : Fin 5, ∑ k : Fin 11,
      ac q0 s i * zc q1 k * bc q2 s k) : K) =
      ((∑ k : Fin 11, (∑ i : Fin 5, ac q0 s i) * zc q1 k * bc q2 s k) : K) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hc, hz]
  ring

end PanLowCoeffSixToNine


theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (s : Fin 2)
    (n : ℕ) (hn6 : 6 ≤ n) (hn10 : n < 10) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff n = 0 := by
  interval_cases n <;>
    simp only [PanLowCoeffSixToNine.side_six,
      PanLowCoeffSixToNine.side_seven, PanLowCoeffSixToNine.side_eight,
      PanLowCoeffSixToNine.side_nine]
