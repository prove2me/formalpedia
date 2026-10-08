-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
-- name    : CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:37:00.992452+00:00
-- url     : https://prove2.me/theorems/f9ba6ded-b08b-495a-afd6-378f7fbba7b8
-- title:
--   Joint concavity and convexity of the Lieb trace expression
-- statement:
--   Let $H$ be a nontrivial finite-dimensional complex Hilbert space and $K$ any bounded operator on $H$. For strictly positive $A,B$, define $F_{s,K}(A,B)=\operatorname{Re}\operatorname{Tr}(A^sK^*B^{1-s}K)$ as in the predecessor part. Strict positivity here means self-adjointness and real spectrum contained in $(0,\infty)$, so the negative power of $B$ occurring when $s>1$ is nonsingular. This part proves joint concavity for $0<s<1$ and joint convexity for $1\le s\le2$. For strictly positive pairs $(A_0,B_0),(A_1,B_1)$ and $0\le\theta\le1$, the concavity inequality is
--   $$
--   F_{s,K}((1-\theta)A_0+\theta A_1,(1-\theta)B_0+\theta B_1)
--    \ge(1-\theta)F_{s,K}(A_0,B_0)+\theta F_{s,K}(A_1,B_1),
--   \qquad 0<s<1,
--   $$
--   and the inequality reverses for $1\le s\le2$. The trace is ordinary and unnormalized; no positivity, invertibility or normalization condition is imposed on $K$.
--
--   The supporting interfaces identify evaluation by $\varphi_K$ of the operator power mean of left multiplication by $A$ and right multiplication by $B$, with power parameters $(s,1)$, with $F_{s,K}(A,B)$. That identity and its weighted-sum form hold for every real $s$ under strict positivity of $A,B$. The part also proves closure of the strictly positive spectral domain under convex combinations; this closure fact itself omits finite dimensionality. The final joint inequalities retain finite dimensionality and nontriviality of $H$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/LiebAndoTrace.lean#L547-L1179

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_1
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/









namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]













































-- This proof is isolated because the joint eigenspace decomposition is heartbeat-heavy.


-- The bridge lemma expands a large `HSOp`-valued generalized perspective term.
set_option backward.isDefEq.respectTransparency false in
 lemma phiK_operatorPowerMean_eq_liebTraceMap
    {s : ℝ} (K A B : L ℋ) (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B)) =
      liebTraceMap (ℋ := ℋ) s K A B := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_half :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((1 : ℝ) / 2)
          (Or.inr (by positivity))).continuousWithinAt)).symm
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBpow :
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2) = B ^ (1 - s) := by
    calc
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)
          = B ^ (((1 : ℝ) / 2) + (-s)) * B ^ ((1 : ℝ) / 2) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ ((((1 : ℝ) / 2) + (-s)) + ((1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (1 - s) := by ring_nf
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    calc
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2)
          = B ^ (((-1 : ℝ) / 2) + ((-1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (-1 : ℝ) := by ring_nf
  have hBinvHalf0 : 0 ≤ B ^ ((-1 : ℝ) / 2) := by
    simp
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hright_invHalf0 :
      0 ≤ rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    exact _root_.LiebAndoTrace.rightMulHS_nonneg (ℋ := ℋ) hBinvHalf0
  have hmid_nonneg :
      0 ≤ cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) := by
    rw [hright_negHalf]
    simpa [mul_assoc] using
      conjugate_nonneg_of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0) hright_invHalf0
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf]
    calc
      rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
          leftMulHS (ℋ := ℋ) A *
          rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))
          =
        leftMulHS (ℋ := ℋ) A *
          (rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))) := by
            rw [← mul_assoc,
              (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
              mul_assoc]
      _ = leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
            rw [← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)), hBnegOne]
  have hmiddle :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
            leftMulHS (ℋ := ℋ) A *
            cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    exact _root_.LiebAndoTrace.hmiddle_leftMul_rightMul (ℋ := ℋ) (s := s) ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩
  have happly :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K)) =
        ofOp (A ^ s * star K * B ^ (1 - s)) := by
    have hcomm_half :
        Commute (leftMulHS (ℋ := ℋ) (A ^ s)) (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) :=
      leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B ^ ((1 : ℝ) / 2))
    have hright_pow :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)) := by
            simp [mul_assoc]
        _ = rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by rw [hBpow]
    have hreorder :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          ((rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              leftMulHS (ℋ := ℋ) (A ^ s)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                simp [mul_assoc]
        _ =
          ((leftMulHS (ℋ := ℋ) (A ^ s) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                rw [hcomm_half.eq]
        _ =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
                simp [mul_assoc]
    calc
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K))
        =
          (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) (ofOp (star K)) := by
            rw [OperatorGeometricMean.operatorPowerMean, GeneralizedPerspective,
              GeneralizedPerspectiveFunction.hSqrt, GeneralizedPerspectiveFunction.hInvSqrt]
            simp only [Real.rpow_one]
            rw [hmiddle]
            rw [hright_half]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) *
              (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
                rightMulHS (ℋ := ℋ) (B ^ (-s)) *
                rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)))) (ofOp (star K)) := by
            rw [hreorder]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (1 - s))) (ofOp (star K)) := by
            rw [hright_pow]
      _ = ofOp (A ^ s * star K * B ^ (1 - s)) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
  calc
    _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [_root_.LiebAndoTrace.phiK, happly]
    _ = traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K) := by
          rw [traceRe]
          set X : L ℋ := A ^ s * star K * B ^ (1 - s)
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ
                  ((K * X).toLinearMap)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) =
                Complex.re (LinearMap.trace ℂ ℋ ((X * K).toLinearMap)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap X.toLinearMap)
          simpa [X, mul_assoc] using htrace'.trans hcycle
    _ = liebTraceMap (ℋ := ℋ) s K A B := by
          rfl

omit [FiniteDimensional ℂ ℋ] in
/-- Convex combinations preserve `pdSet` (strict positivity). -/
lemma pdSet_convexCombo {A B : L ℋ} {t : ℝ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA_sa |>.add ((IsSelfAdjoint.all t).smul hB_sa)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 ?_
    intro x hx
    exact hA_spec hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB_sa)).2 ?_
    intro x hx
    exact hB_spec hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      simpa [rC] using
        add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  refine ⟨hC, ?_⟩
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx









 lemma phiK_weightedSum_operatorPowerMean_eq
    {s θ : ℝ} (K A₁ A₂ B₁ B₂ : L ℋ)
    (hA₁ : A₁ ∈ pdSet (ℋ := ℋ)) (hA₂ : A₂ ∈ pdSet (ℋ := ℋ))
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ)) :
    _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
        ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) • liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ • liebTraceMap (ℋ := ℋ) s K A₂ B₂ := by
  rw [_root_.LiebAndoTrace.phiK_add, _root_.LiebAndoTrace.phiK_smul, _root_.LiebAndoTrace.phiK_smul]
  simpa [smul_eq_mul] using
    show (1 - θ) * _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁)) +
      θ * _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) * liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ * liebTraceMap (ℋ := ℋ) s K A₂ B₂ by
      simp only [_root_.LiebAndoTrace.phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₁ B₁ hA₁ hB₁,
    _root_.LiebAndoTrace.phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₂ B₂ hA₂ hB₂]

-- The `HSOp`-valued `operatorPowerMean` terms are large enough
-- that the skeleton itself is expensive.
theorem liebTrace_jointlyConcaveOn_pdSet
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    change ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    change ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconc_hs :=
    operatorPowerMean_jointlyConcaveOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (_root_.LiebAndoTrace.rightMulHS_pdSet (ℋ := ℋ) hB₁) (_root_.LiebAndoTrace.rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconc :
      (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
        θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) ≤
        operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) := by
    simpa [hleft_combo, hright_combo] using hconc_hs
  have hphi_mono :
      _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) ≤
        _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) := by
    exact _root_.LiebAndoTrace.phiK_mono (ℋ := ℋ) K hconc
  rw [_root_.LiebAndoTrace.phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  rw [_root_.LiebAndoTrace.phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

theorem liebTrace_jointlyConvexOn_pdSet
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    change ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    change ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconv_hs :=
    operatorPowerMean_jointlyConvexOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨hs1, hs2⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (_root_.LiebAndoTrace.rightMulHS_pdSet (ℋ := ℋ) hB₁) (_root_.LiebAndoTrace.rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconv :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) ≤
        (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) := by
    simpa [hleft_combo, hright_combo] using hconv_hs
  have hphi_mono :
      _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) ≤
        _root_.LiebAndoTrace.phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) := by
    exact _root_.LiebAndoTrace.phiK_mono (ℋ := ℋ) K hconv
  rw [_root_.LiebAndoTrace.phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  rw [_root_.LiebAndoTrace.phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono
end LiebAndoTrace


