-- Prove2me | solution 1 for LinearOptimization.lp_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:59:06.180011+00:00
-- url     : https://prove2.me/submissions/63ae90cd-09c3-4ff4-b47f-6dc161835686

import Definitions.Def_LinearOptimization_DualLP
import Mathlib.Tactic.Linarith

open Matrix

theorem solution {m n : ℕ} (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.generalFeasibleSet P)
    (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) :
    p ⬝ᵥ P.b ≤ P.c ⬝ᵥ x := by
  classical
  rcases hx with ⟨hxrow, hxsign⟩
  rcases hp with ⟨hprow, hpsign⟩
  have hrow (i : Fin m) : 0 ≤ p i * (P.A i ⬝ᵥ x - P.b i) := by
    have hxi := hxrow i
    have hpi := hpsign i
    cases hrel : P.rowRel i with
    | ge =>
        simp [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
          LinearOptimization.VarSign.IsSatisfiedBy, hrel] at hpi
        simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
        exact mul_nonneg hpi (sub_nonneg.mpr hxi)
    | le =>
        simp [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
          LinearOptimization.VarSign.IsSatisfiedBy, hrel] at hpi
        simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
        exact mul_nonneg_of_nonpos_of_nonpos hpi (sub_nonpos.mpr hxi)
    | eq =>
        simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
        simp [hxi]
  have hcol (j : Fin n) :
      0 ≤ (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j := by
    have hpj := hprow j
    have hxj := hxsign j
    have hneg : (-P.Aᵀ) j ⬝ᵥ p = -(p ⬝ᵥ (fun i ↦ P.A i j)) := by
      simp [dotProduct, mul_comm]
    cases hsign : P.colSign j with
    | nonneg =>
        simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
        simp [LinearOptimization.VarSign.IsSatisfiedBy, hsign] at hxj
        exact mul_nonneg (sub_nonneg.mpr hpj) hxj
    | nonpos =>
        simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
        simp [LinearOptimization.VarSign.IsSatisfiedBy, hsign] at hxj
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpj) hxj
    | free =>
        simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
        simp [hpj]
  have hrowsum : 0 ≤ ∑ i : Fin m, p i * (P.A i ⬝ᵥ x - P.b i) :=
    Finset.sum_nonneg fun i hi ↦ hrow i
  have hcolsum : 0 ≤
      ∑ j : Fin n, (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j :=
    Finset.sum_nonneg fun j hj ↦ hcol j
  have hid :
      (∑ i : Fin m, p i * (P.A i ⬝ᵥ x - P.b i)) +
        (∑ j : Fin n, (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j) =
      P.c ⬝ᵥ x - p ⬝ᵥ P.b := by
    simp only [dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [show (∑ i : Fin m, p i * ∑ j : Fin n, P.A i j * x j) =
        ∑ j : Fin n, (∑ i : Fin m, p i * P.A i j) * x j by
      calc
        (∑ i : Fin m, p i * ∑ j : Fin n, P.A i j * x j) =
            ∑ i : Fin m, ∑ j : Fin n, p i * (P.A i j * x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ j : Fin n, ∑ i : Fin m, p i * (P.A i j * x j) :=
          Finset.sum_comm
        _ = ∑ j : Fin n, (∑ i : Fin m, p i * P.A i j) * x j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
    ring
  linarith
