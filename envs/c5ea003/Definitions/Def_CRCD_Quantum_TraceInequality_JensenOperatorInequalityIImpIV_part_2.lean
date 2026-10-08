-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
-- name    : CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:03:42.809265+00:00
-- url     : https://prove2.me/theorems/732988dc-b3ed-4c1d-a1cd-0a7c1e1586b5
-- title:
--   Uniform operator convexity implies Jensen inequality for a contraction
-- statement:
--   Let $H$ be a nontrivial complete complex Hilbert space and $f:\mathbb R\to\mathbb R$. Assume that $f$ is operator convex on $[0,\infty)$ for bounded operators on every nontrivial complete complex Hilbert space in the same universe, that $f$ is continuous on $[0,\infty)$, and that $f(0)\le0$. This part proves the previously defined single-contraction Jensen condition: every self-adjoint bounded operator $A$ on $H$ with real spectrum in $[0,\infty)$, and every bounded operator $X$ on $H$ with $\|X\|\le1$, satisfy
--   $$
--   f(X^*AX)\le X^*f(A)X.
--   $$
--   Both sides use the real continuous functional calculus and the standard positive-operator order. The theorem requires the uniform convexity hypothesis, so it applies the convexity property on the auxiliary Hilbert direct sum as well as on $H$. No finite-dimensional assumption, invertibility assumption on $A$, or unitarity assumption on $X$ is required. This part contains the implication itself; the predicates and block-operator interfaces are supplied by its predecessor.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/JensenOperatorInequalityIImpIV.lean#L551-L805

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_1
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/






set_option linter.style.longLine false

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]



































-- Converting positivity on a block-diagonal operator to each diagonal block is expensive.
































-- `simp` and normalization over block expressions are expensive here.









--Theorem 2.5.2 `(i) → (iv)`.

set_option maxHeartbeats 2000000 in
-- The localized proof duplicates the block-matrix normalization from the global theorem.
theorem theorem_2_5_2_i_ici_all_imp_iv {f : ℝ → ℝ} (hf : CondIciAll.{u} f) :
    CondIV (ℋ := ℋ) f := by
  rcases hf with ⟨hconvAll, hcontIci, hf0⟩
  intro A X hA hAs hX
  have hconv : OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f := hconvAll (K := ℋ)
  have hA0 : (0 : L ℋ) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    simpa [Set.Ici] using hAs hx
  let S : L (HSum ℋ) := _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X
  have hSsa : IsSelfAdjoint S := by
    change star S = S
    simpa [S] using _root_.JensenOperatorInequality.blockSwap_star (ℋ := ℋ) X
  have hSnorm : ‖S‖ ≤ 1 := by
    simpa [S] using _root_.JensenOperatorInequality.blockSwap_norm_le_one (ℋ := ℋ) X hX
  letI : Algebra ℝ (L (HSum ℋ)) := by
    infer_instance
  have hU_mem : S + Complex.I • CFC.sqrt (1 - S ^ 2) ∈ unitary (L (HSum ℋ)) := by
    exact IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary S hSsa hSnorm
  let U : unitary (L (HSum ℋ)) :=
    ⟨S + Complex.I • CFC.sqrt (1 - S ^ 2), hU_mem⟩
  let V : unitary (L (HSum ℋ)) := star U
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) 0 A
  letI : Nontrivial (L (HSum ℋ)) := _root_.JensenOperatorInequality.nontrivial_hsumL (ℋ := ℋ)
  have hconv₂ : OperatorConvexOn (ℋ := HSum ℋ) (Set.Ici (0 : ℝ)) f :=
    hconvAll (K := HSum ℋ)
  have hR0nonneg : (0 : L ℋ) ≤ 1 - star X * X := sub_nonneg.mpr (_root_.JensenOperatorInequality.star_mul_le_one (ℋ := ℋ) X hX)
  have hR1nonneg : (0 : L ℋ) ≤ 1 - X * star X := sub_nonneg.mpr (_root_.JensenOperatorInequality.mul_star_le_one (ℋ := ℋ) X hX)
  let R0 : L ℋ := CFC.sqrt (1 - star X * X)
  let R1 : L ℋ := CFC.sqrt (1 - X * star X)
  have hR0sa : IsSelfAdjoint (1 - star X * X) := by
    change star (1 - star X * X) = 1 - star X * X
    simp
  have hR1sa : IsSelfAdjoint (1 - X * star X) := by
    change star (1 - X * star X) = 1 - X * star X
    simp
  have hSsq : S ^ 2 = blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [pow_two, S] using _root_.JensenOperatorInequality.blockSwap_sq (ℋ := ℋ) X
  have hOneMinusSq :
      1 - S ^ 2 = blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) := by
    rw [hSsq]
    refine blockOp_ext (ℋ := ℋ) ?_ ?_
    · intro z
      simp [sub_eq_add_neg, add_comm]
    · intro z
      simp [sub_eq_add_neg, add_comm]
  have hOneMinusSqNonneg : (0 : L (HSum ℋ)) ≤ 1 - S ^ 2 := by
    have hdiag : (0 : L (HSum ℋ)) ≤
        blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      blockDiagonal_nonneg (ℋ := ℋ) hR0nonneg hR1nonneg
    simpa [hOneMinusSq] using hdiag
  have hRblock : CFC.sqrt (1 - S ^ 2) = blockDiagonal (ℋ := ℋ) R0 R1 := by
    rw [hOneMinusSq]
    simp [R0, R1]
    simpa using
      (_root_.JensenOperatorInequality.sqrt_blockDiagonal_of_nonneg (ℋ := ℋ) (A := 1 - star X * X) (B := 1 - X * star X)
        hR0sa hR1sa hR0nonneg hR1nonneg)
  have hR0self : IsSelfAdjoint R0 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - star X * X)) :=
      (CFC.sqrt_nonneg (1 - star X * X)).isSelfAdjoint
    simpa [R0] using h
  have hR1self : IsSelfAdjoint R1 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - X * star X)) :=
      (CFC.sqrt_nonneg (1 - X * star X)).isSelfAdjoint
    simpa [R1] using h
  have hU_block :
      (U : L (HSum ℋ)) = blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
    change S + Complex.I • CFC.sqrt (1 - S ^ 2) = _
    rw [hRblock]
    simpa [S] using _root_.JensenOperatorInequality.blockSwap_add_I_smul_blockDiagonal (ℋ := ℋ) X R0 R1
  have hV_block :
      (V : L (HSum ℋ)) = blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1) := by
    change star (U : L (HSum ℋ)) = _
    rw [hU_block]
    ext z i
    fin_cases i <;>
      simp [blockOp_star, hR0self.star_eq, hR1self.star_eq]
  have hB1_block :
      (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (Complex.I • R1))
          ((-Complex.I • R1) * A * X)
          ((-Complex.I • R1) * A * (Complex.I • R1)) := by
    rw [show (star U : L (HSum ℋ)) = (V : L (HSum ℋ)) by rfl, hV_block, hU_block]
    simpa [Atilde, mul_assoc] using
      (_root_.JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (-Complex.I • R0) (star X) X (-Complex.I • R1) A
        (Complex.I • R0) (star X) X (Complex.I • R1))
  have hB2_block :
      (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (-Complex.I • R1))
          ((Complex.I • R1) * A * X)
          ((Complex.I • R1) * A * (-Complex.I • R1)) := by
    rw [show (star V : L (HSum ℋ)) = (U : L (HSum ℋ)) by simp [V], hU_block, hV_block]
    simpa [Atilde, mul_assoc] using
      (_root_.JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (Complex.I • R0) (star X) X (Complex.I • R1) A
        (-Complex.I • R0) (star X) X (-Complex.I • R1))
  have hmid_block :
      (1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) +
          (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) =
        blockDiagonal (ℋ := ℋ) (star X * A * X) (R1 * A * R1) := by
    rw [hB1_block, hB2_block]
    rw [_root_.JensenOperatorInequality.blockOp_smulR, _root_.JensenOperatorInequality.blockOp_smulR, _root_.JensenOperatorInequality.blockOp_add, _root_.JensenOperatorInequality.blockDiagonal_eq_blockOp]
    congr 1
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (star X * A * X) + (1 / 2 : ℝ) • (star X * A * X)
            = (2⁻¹ + 2⁻¹ : ℝ) • (star X * (A * X)) := by
                simp [add_smul, mul_assoc]
        _ = (1 : ℝ) • (star X * (A * X)) := by rw [hhalf]
        _ = star X * (A * X) := by simp
        _ = star X * A * X := by simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (-Complex.I • R1 * A * (Complex.I • R1)) +
            (1 / 2 : ℝ) • (Complex.I • R1 * A * (-Complex.I • R1))
            = (2⁻¹ + 2⁻¹ : ℝ) • (R1 * (A * R1)) := by
                simp [Complex.I_mul_I, smul_smul, add_smul, mul_assoc]
        _ = (1 : ℝ) • (R1 * (A * R1)) := by rw [hhalf]
        _ = R1 * A * R1 := by simp [mul_assoc]
  have hAtilde_sa : IsSelfAdjoint Atilde := by
    simpa [Atilde] using _root_.JensenOperatorInequality.blockDiagonal_selfAdjoint (ℋ := ℋ) (hA := by simp) hA
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := by
    simpa [Atilde] using blockDiagonal_nonneg (ℋ := ℋ) (show (0 : L ℋ) ≤ 0 by simp) hA0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) := _root_.JensenOperatorInequality.spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hAtilde0
  have hB1_nonneg : (0 : L (HSum ℋ)) ≤ (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hAtilde0 (U : L (HSum ℋ))
  have hB2_nonneg : (0 : L (HSum ℋ)) ≤ (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hAtilde0 (V : L (HSum ℋ))
  have hB1_sa : IsSelfAdjoint ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) :=
    IsSelfAdjoint.of_nonneg hB1_nonneg
  have hB2_sa : IsSelfAdjoint ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) :=
    IsSelfAdjoint.of_nonneg hB2_nonneg
  have hB1_spec : spectrum ℝ ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) ⊆ Set.Ici (0 : ℝ) :=
    _root_.JensenOperatorInequality.spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB1_nonneg
  have hB2_spec : spectrum ℝ ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) ⊆ Set.Ici (0 : ℝ) :=
    _root_.JensenOperatorInequality.spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB2_nonneg
  have hmid_conv :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) ≤
        ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
          (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) := by
    have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
    simpa [hhalf] using
      (hconv₂
        (A := (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)))
        (B := (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))
        (t := (1 / 2 : ℝ))
        hB1_sa hB2_sa (by positivity) (by norm_num) hB1_spec hB2_spec)
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f 0) (cfcR (ℋ := ℋ) f A) := by
    simpa [Atilde] using
      (_root_.JensenOperatorInequality.cfcR_blockDiagonal (ℋ := ℋ) (f := f) (A := 0) (B := A) (by simp) hA
        (_root_.JensenOperatorInequality.continuousOn_union_of_subset_Ici (f := f) hcontIci
          (s := spectrum ℝ (0 : L ℋ)) (t := spectrum ℝ A)
          _root_.JensenOperatorInequality.spectrum_zero_subset_Ici hAs))
  have hUcfc :
      cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) =
        (star U : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (U : L (HSum ℋ)) := by
    simpa [mul_assoc] using
      _root_.JensenOperatorInequality.cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcontIci
        hAtilde_spec U hAtilde_sa
  have hVcfc :
      cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) ) =
        (star V : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (V : L (HSum ℋ)) := by
    simpa [mul_assoc] using
      _root_.JensenOperatorInequality.cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcontIci
        hAtilde_spec V hAtilde_sa
  have hLeftEval :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f (star X * A * X)) (cfcR (ℋ := ℋ) f (R1 * A * R1)) := by
    have hXAX_nonneg : (0 : L ℋ) ≤ star X * A * X := by
      simpa [mul_assoc] using star_left_conjugate_nonneg hA0 X
    have hR1AR1_nonneg : (0 : L ℋ) ≤ R1 * A * R1 := by
      simpa [hR1self.star_eq, mul_assoc] using star_right_conjugate_nonneg hA0 R1
    have hXAX_sa : IsSelfAdjoint (star X * A * X) := IsSelfAdjoint.of_nonneg hXAX_nonneg
    have hR1AR1_sa : IsSelfAdjoint (R1 * A * R1) := IsSelfAdjoint.of_nonneg hR1AR1_nonneg
    have hXAX_spec : spectrum ℝ (star X * A * X) ⊆ Set.Ici (0 : ℝ) :=
      _root_.JensenOperatorInequality.spectrum_Ici_of_nonneg (ℋ := ℋ) hXAX_nonneg
    have hR1AR1_spec : spectrum ℝ (R1 * A * R1) ⊆ Set.Ici (0 : ℝ) :=
      _root_.JensenOperatorInequality.spectrum_Ici_of_nonneg (ℋ := ℋ) hR1AR1_nonneg
    rw [hmid_block]
    refine _root_.JensenOperatorInequality.cfcR_blockDiagonal (ℋ := ℋ) (f := f) (A := star X * A * X) (B := R1 * A * R1)
      hXAX_sa hR1AR1_sa ?_
    exact _root_.JensenOperatorInequality.continuousOn_union_of_subset_Ici (f := f) hcontIci hXAX_spec hR1AR1_spec
  have hRightEval :
      ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
        (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hUcfc, hVcfc, hAtilde_cfc, _root_.JensenOperatorInequality.cfcR_zero]
    rw [hU_block, hV_block, _root_.JensenOperatorInequality.blockDiagonal_eq_blockOp]
    rw [blockOp_star, blockOp_star]
    simp_rw [mul_assoc]
    rw [_root_.JensenOperatorInequality.blockOp_mul, _root_.JensenOperatorInequality.blockOp_mul, _root_.JensenOperatorInequality.blockOp_mul, _root_.JensenOperatorInequality.blockOp_mul]
    rw [_root_.JensenOperatorInequality.blockOp_smulR, _root_.JensenOperatorInequality.blockOp_smulR, _root_.JensenOperatorInequality.blockOp_add, _root_.JensenOperatorInequality.blockDiagonal_eq_blockOp]
    have hTopLeft :
        (2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
            ((2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
              (-((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)) +
                -((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)))) =
          star X * (cfcR (ℋ := ℋ) f A * X) + (f 0) • (R0 * R0) := by
      simpa using
        _root_.JensenOperatorInequality.rightEval_topLeft_scalar (ℋ := ℋ) (r := f 0) (R0 := R0) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    have hBottomRight :
        (2⁻¹ * f 0) • (X * star X) +
            ((2⁻¹ * f 0) • (X * star X) +
              ((2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)) +
                (2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)))) =
          (R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X) := by
      simpa [mul_assoc] using
        _root_.JensenOperatorInequality.rightEval_bottomRight_scalar (ℋ := ℋ) (r := f 0) (R1 := R1) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    congr 1
    · simpa [hR0self.star_eq, Algebra.algebraMap_eq_smul_one, mul_assoc,
        add_assoc, add_left_comm, add_comm] using hTopLeft
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simpa [hR1self.star_eq, Algebra.algebraMap_eq_smul_one, Complex.I_mul_I, smul_smul,
        mul_assoc, add_assoc, add_left_comm, add_comm] using hBottomRight
  have hcore :
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f (star X * A * X)) (cfcR (ℋ := ℋ) f (R1 * A * R1)) ≤
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hLeftEval, hRightEval] at hmid_conv
    exact hmid_conv
  have hterm_nonpos : (f 0) • (R0 * R0) ≤ (0 : L ℋ) := by
    have hR0sq_nonneg : (0 : L ℋ) ≤ R0 * R0 := by
      simpa [hR0self.star_eq] using star_mul_self_nonneg R0
    have hneg : (0 : L ℋ) ≤ (- (f 0)) • (R0 * R0) := by
      exact smul_nonneg (by linarith [hf0]) hR0sq_nonneg
    exact (neg_nonneg.mp (by simpa [neg_smul] using hneg))
  have htop :
      cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) := by
    exact _root_.JensenOperatorInequality.blockDiagonal_le_left (ℋ := ℋ) hcore
  have hdrop :
      star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) ≤ star X * cfcR (ℋ := ℋ) f A * X := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hterm_nonpos (star X * cfcR (ℋ := ℋ) f A * X)
  exact htop.trans hdrop
end Theorem252
end JensenOperatorInequality


