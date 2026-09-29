-- Prove2me | solution 1 for mme_six_square_family_product_weight
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:30:48.308507+00:00
-- url     : https://prove2.me/submissions/5774ba7b-66e6-4490-8c3b-a5323e14d841

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators
universe u
set_option autoImplicit false

private theorem kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright


private theorem six_kron_iso {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kron (sixSymmetrization X) (sixSymmetrization Y))
      (sixSymmetrization (TensorObj.kron X Y)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  ring

/-- A square boundary extraction multiplies every interior matrix dimension
without changing the number of summands or losing exponential weight. -/
theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3} {q : ℕ}
    (M : ℕ) (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ)
    (hboundary : TensorObj.Restrict (MMObj K M M M) (sixSymmetrization X))
    (hinterior : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) (sixSymmetrization Y))
    (hboundaryWeight : Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau)
    (hinteriorWeight : Real.exp interiorRate ≤
      ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (sixSymmetrization (TensorObj.kron X Y)) ∧
    Real.exp (boundaryRate + interiorRate) ≤
      ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  have hdist : TensorObj.Isomorphic
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (TensorObj.kron (MMObj K M M M)
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))) := by
    rw [← TensorQ.toQ_eq_iff, TensorQ.toQ_kron, TensorQ.toQ_bigAdd,
      TensorQ.toQ_bigAdd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K)
      M M M (a i) (b i) (c i))).symm.trans (TensorQ.toQ_kron _ _)
  constructor
  · exact hdist.1.trans ((kron_restrict_for_tau_product (by decide)
      hboundary hinterior).trans (six_kron_iso X Y).1)
  · rw [Real.exp_add]
    have hmul := mul_le_mul hboundaryWeight hinteriorWeight
      (Real.exp_pos interiorRate).le (Real.rpow_nonneg (by positivity) tau)
    calc
      Real.exp boundaryRate * Real.exp interiorRate ≤
          ((M * M * M : ℕ) : ℝ) ^ tau *
            ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau := hmul
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        push_cast
        ring


#print axioms solution
