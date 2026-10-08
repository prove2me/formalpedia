-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
-- name    : CRCD_QuantumChannelContinuity_Schatten
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:12:40.468327+00:00
-- url     : https://prove2.me/theorems/beb87f1a-305a-4bba-8963-3afd49e7da4e
-- title:
--   Coefficient operators and Schatten decomposition interfaces
-- statement:
--   For a rectangular complex-linear coefficient map $C:E\to F$, its positive output operator is $CC^*$, with no trace-one normalization imposed. Its Hilbert–Schmidt coordinate vector is $(C e_j)_j$ in the standard orthonormal basis of $E$. Vectorization gives a complex-linear equivalence between $F\otimes E$ and coefficient maps $E\to F$, preserving sums and all cross terms. These interfaces support trace-power and weighted Schatten estimates for coefficient decompositions. The sandwiched Rényi decomposition bound uses $1<p\le2$ and explicit positive semidefinite comparison operators and nonnegative weights; it is used only in this order range near one.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/Schatten.lean#L28-L644

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Trace Hölder and the coefficient-matrix bridge

These are concrete finite-dimensional operator inequalities used in the
manuscript's Schatten estimate. They have no analytic assumptions hidden in a
structure: Hölder's inequality for positive operators follows from their
orthonormal eigenbases and scalar Hölder.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped TensorProduct
open scoped BigOperators ComplexOrder MatrixOrder NNReal

set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

/-- Scalar Hölder with doubly stochastic overlap weights. Zero weights and zero
vectors are allowed. -/
theorem weighted_holder_finset {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (x : ι → ℝ) (y : κ → ℝ) (c : ι → κ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (hc : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, (∑ j, c i j) = 1) (hcol : ∀ j, (∑ i, c i j) = 1) :
    (∑ i, ∑ j, x i * y j * c i j) ≤
      (∑ i, x i ^ p) ^ (1 / p) * (∑ j, y j ^ q) ^ (1 / q) := by
  classical
  let f : ι × κ → ℝ := fun z => x z.1 * (c z.1 z.2) ^ (1 / p)
  let g : ι × κ → ℝ := fun z => y z.2 * (c z.1 z.2) ^ (1 / q)
  have hfg (i : ι) (j : κ) : f (i,j) * g (i,j) = x i * y j * c i j := by
    dsimp [f, g]
    calc
      x i * c i j ^ (1 / p) * (y j * c i j ^ (1 / q)) =
          x i * y j * (c i j ^ (1 / p) * c i j ^ (1 / q)) := by ring
      _ = x i * y j * c i j := by
        rw [← Real.rpow_add_of_nonneg (hc i j) hpq.one_div_nonneg
          hpq.symm.one_div_nonneg, hpq.one_div_add_one_div, div_one, Real.rpow_one]
  have hfp (i : ι) (j : κ) : f (i,j) ^ p = x i ^ p * c i j := by
    dsimp [f]
    rw [Real.mul_rpow (hx i) (Real.rpow_nonneg (hc i j) _),
      ← Real.rpow_mul (hc i j), one_div_mul_cancel hpq.ne_zero, Real.rpow_one]
  have hgq (i : ι) (j : κ) : g (i,j) ^ q = y j ^ q * c i j := by
    dsimp [g]
    rw [Real.mul_rpow (hy j) (Real.rpow_nonneg (hc i j) _),
      ← Real.rpow_mul (hc i j), one_div_mul_cancel hpq.symm.ne_zero, Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (ι × κ)) hpq
      (f := f) (g := g)
      (fun z _ => mul_nonneg (hx z.1) (Real.rpow_nonneg (hc z.1 z.2) _))
      (fun z _ => mul_nonneg (hy z.2) (Real.rpow_nonneg (hc z.1 z.2) _))
  have hleft : (∑ z, f z * g z) = ∑ i, ∑ j, x i * y j * c i j := by
    simp_rw [Fintype.sum_prod_type, hfg]
  have hfirst : (∑ z, f z ^ p) = ∑ i, x i ^ p := by
    simp_rw [Fintype.sum_prod_type, hfp, ← Finset.mul_sum, hrow, mul_one]
  have hsecond : (∑ z, g z ^ q) = ∑ j, y j ^ q := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [hgq, ← Finset.mul_sum, hcol, mul_one]
  simpa only [hleft, hfirst, hsecond] using h

/-- Trace Hölder for positive semidefinite operators, including singular
operators. The Schatten powers appear as actual functional-calculus traces. -/
theorem trace_holder {ℋ : Type*} [Qudit ℋ] {p q : ℝ}
    (hpq : p.HolderConjugate q) (X Y : L ℋ)
    (hX : X.IsPositive) (hY : Y.IsPositive) :
    (Tr (X ∘ₗ Y)).re ≤
      (Tr (CFC.rpow X p)).re ^ (1 / p) *
      (Tr (CFC.rpow Y q)).re ^ (1 / q) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let by' := hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let x := hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl
  let y := hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl
  have h := weighted_holder_finset hpq x y (fun i j => ‖inner ℂ (bx i) (by' j)‖ ^ 2)
    (fun i => hX.nonneg_eigenvalues (hn := rfl) i)
    (fun j => hY.nonneg_eigenvalues (hn := rfl) j)
    (overlap_coeff_nonneg bx by') (overlap_coeff_row_sum bx by')
    (overlap_coeff_col_sum bx by')
  rw [trace_rpow_eq_sum_eigenvalues X hX p hpq.nonneg,
    trace_rpow_eq_sum_eigenvalues Y hY q hpq.symm.nonneg]
  simp only [Complex.ofReal_re]
  rw [trace_comp_eq_double_sum_eigen_overlap X Y hX hY]
  have heq :
      (∑ j, (y j : ℂ) * (∑ i, (x i : ℂ) *
        (Complex.normSq (inner ℂ (bx i) (by' j)) : ℂ))).re =
      ∑ i, ∑ j, x i * y j * ‖inner ℂ (bx i) (by' j)‖ ^ 2 := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Finset.mul_sum, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ j, (y j : ℂ) * (∑ i, (x i : ℂ) *
        (Complex.normSq (inner ℂ (bx i) (by' j)) : ℂ))).re ≤ _
  rw [heq]
  exact h

section CoefficientMaps

variable {E F : Type*} [Qudit E] [Qudit F]

/-- Density operator obtained by discarding the environment of a coefficient map. -/
noncomputable def coefficientDensity (C : E →ₗ[ℂ] F) : L F :=
  C ∘ₗ C.adjoint

/-- The partial-trace density is positive without normalization assumptions. -/
theorem coefficientDensity_pos (C : E →ₗ[ℂ] F) : (coefficientDensity C).IsPositive :=
  LinearMap.isPositive_self_comp_adjoint C

/-- Hilbert-Schmidt coordinates of a rectangular coefficient map. -/
noncomputable def coefficientVector (C : E →ₗ[ℂ] F) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ E) => F) :=
  WithLp.toLp 2 (fun j => C (stdOrthonormalBasis ℂ E j))

/-- The norm of the coefficient vector is exactly the square root of the output trace. -/
theorem coefficientVector_norm_sq (C : E →ₗ[ℂ] F) :
    ‖coefficientVector C‖ ^ 2 = (Tr (coefficientDensity C)).re := by
  rw [coefficientDensity, ← LinearMap.trace_comp_comm' C C.adjoint]
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)]
  simp only [coefficientVector, PiLp.norm_sq_eq_of_L2,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm



/-- The Hilbert-Schmidt triangle inequality expressed in terms of the actual
partial-trace coefficient densities. -/
theorem coefficient_trace_triangle {ι : Type*} [Fintype ι]
    (C : ι → E →ₗ[ℂ] F) :
    Real.sqrt (Tr (coefficientDensity (∑ i, C i))).re ≤
      ∑ i, Real.sqrt (Tr (coefficientDensity (C i))).re := by
  have hnorm (D : E →ₗ[ℂ] F) :
      Real.sqrt (Tr (coefficientDensity D)).re = ‖coefficientVector D‖ := by
    rw [← coefficientVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hnorm]
  have hsum : coefficientVector (∑ i, C i) = ∑ i, coefficientVector (C i) := by
    ext j
    simp [coefficientVector]
  rw [hsum]
  exact norm_sum_le _ _

/-- Trace of a weighted coefficient density is the square of a genuine Hilbert
space norm. This identity also proves nonnegativity of the weighted trace. -/
theorem coefficient_trace_weight (S : L F) (C : E →ₗ[ℂ] F) :
    Tr (coefficientDensity (S ∘ₗ C)) =
      Tr ((S.adjoint ∘ₗ S) ∘ₗ coefficientDensity C) := by
  unfold coefficientDensity
  rw [LinearMap.adjoint_comp]
  have h := LinearMap.trace_comp_cycle' (C ∘ₗ C.adjoint) S S.adjoint
  simpa only [LinearMap.comp_assoc] using h

/-- Weighted coefficient-map triangle inequality. It keeps all cross terms and
allows rectangular maps and singular weights. -/
theorem weighted_coefficient_triangle {ι : Type*} [Fintype ι]
    (H : L F) (hH : H.IsPositive) (C : ι → E →ₗ[ℂ] F) :
    Real.sqrt (Tr (H ∘ₗ coefficientDensity (∑ i, C i))).re ≤
      ∑ i, Real.sqrt (Tr (H ∘ₗ coefficientDensity (C i))).re := by
  let S : L F := CFC.sqrt H
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive S).1 (CFC.sqrt_nonneg H)
  have hSS : S.adjoint ∘ₗ S = H := by
    rw [hS.adjoint_eq]
    change S * S = H
    exact CFC.sqrt_mul_sqrt_self H ((LinearMap.nonneg_iff_isPositive H).2 hH)
  have htrace (D : E →ₗ[ℂ] F) :
      Tr (coefficientDensity (S ∘ₗ D)) = Tr (H ∘ₗ coefficientDensity D) := by
    rw [coefficient_trace_weight, hSS]
  have h := coefficient_trace_triangle (fun i => S ∘ₗ C i)
  have hsum : (∑ i, S ∘ₗ C i) = S ∘ₗ ∑ i, C i := by
    ext v
    simp
  rw [hsum] at h
  simpa only [htrace] using h

/-- Nonnegative functional-calculus powers have nonnegative real trace. -/
theorem trace_rpow_re_nonneg (X : L F) (p : ℝ) :
    0 ≤ (Tr (CFC.rpow X p)).re := by
  have hX : (CFC.rpow X p).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  exact (Complex.nonneg_iff.mp hX.trace_nonneg).1

/-- The dual test operator `X^(p-1)` attains the trace-power pairing, including
when `X` is singular. Only positive exponents are multiplied. -/
theorem rpow_sub_one_mul_self (X : L F) (hX : X.IsPositive) {p : ℝ} (hp : 1 < p) :
    CFC.rpow X (p - 1) * X = CFC.rpow X p := by
  have hX0 : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2 hX
  let s : NNReal := ⟨p - 1, by linarith⟩
  let r : NNReal := ⟨p, by linarith⟩
  have hs : (0 : NNReal) < s := by exact_mod_cast (show (0 : ℝ) < p - 1 by linarith)
  have hr : (0 : NNReal) < r := by exact_mod_cast (show (0 : ℝ) < p by linarith)
  have hsr : s + 1 = r := by
    ext
    change (p - 1) + 1 = p
    ring
  change CFC.rpow X (↑s : ℝ) * X = CFC.rpow X (↑r : ℝ)
  simp only [CFC.rpow_eq_pow]
  conv_lhs => rhs; rw [show X = X ^ (1 : NNReal) from by
    rw [CFC.nnrpow_eq_rpow one_pos, NNReal.coe_one]; exact (CFC.rpow_one X hX0).symm]
  rw [← CFC.nnrpow_eq_rpow hs, ← CFC.nnrpow_eq_rpow hr,
    ← CFC.nnrpow_add hs one_pos, hsr]

/-- Schatten `2p` triangle inequality for arbitrary finite families of rectangular
coefficient maps. This is the precise analytic triangle needed in the paper;
no invertibility or full-rank hypothesis is imposed. -/
theorem schatten_coefficient_triangle {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (C : ι → E →ₗ[ℂ] F) :
    (Tr (CFC.rpow (coefficientDensity (∑ i, C i)) p)).re ^ (1 / (2 * p)) ≤
      ∑ i, (Tr (CFC.rpow (coefficientDensity (C i)) p)).re ^ (1 / (2 * p)) := by
  let X : L F := coefficientDensity (∑ i, C i)
  let H : L F := CFC.rpow X (p - 1)
  let R : ℝ := (Tr (CFC.rpow X p)).re
  let Q : ι → ℝ := fun i => (Tr (CFC.rpow (coefficientDensity (C i)) p)).re
  let q : ℝ := p / (p - 1)
  have hX : X.IsPositive := coefficientDensity_pos _
  have hH : H.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hR : 0 ≤ R := trace_rpow_re_nonneg X p
  have hQ : ∀ i, 0 ≤ Q i := fun i => trace_rpow_re_nonneg _ p
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have hpq : p.HolderConjugate q :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hHq : CFC.rpow H q = CFC.rpow X p := by
    dsimp only [H]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X (p - 1) q hpm1.le hpq.symm.nonneg
      ((LinearMap.nonneg_iff_isPositive _).2 hX)]
    congr 1
    dsimp [q]
    field_simp
  have hHX : H ∘ₗ X = CFC.rpow X p := rpow_sub_one_mul_self X hX hp
  have hstart : Real.sqrt R ≤
      ∑ i, Real.sqrt (Tr (H ∘ₗ coefficientDensity (C i))).re := by
    have h := weighted_coefficient_triangle H hH C
    change Real.sqrt (Tr (H ∘ₗ X)).re ≤ _ at h
    rwa [hHX] at h
  have hterm (i : ι) :
      Real.sqrt (Tr (H ∘ₗ coefficientDensity (C i))).re ≤
        R ^ (1 / (2 * q)) * Q i ^ (1 / (2 * p)) := by
    have ht := trace_holder hpq.symm H (coefficientDensity (C i)) hH
      (coefficientDensity_pos _)
    rw [hHq] at ht
    change (Tr (H ∘ₗ coefficientDensity (C i))).re ≤ R ^ (1 / q) * Q i ^ (1 / p) at ht
    calc
      Real.sqrt (Tr (H ∘ₗ coefficientDensity (C i))).re ≤
          Real.sqrt (R ^ (1 / q) * Q i ^ (1 / p)) := Real.sqrt_le_sqrt ht
      _ = R ^ (1 / (2 * q)) * Q i ^ (1 / (2 * p)) := by
        rw [Real.sqrt_mul (Real.rpow_nonneg hR _)]
        simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hR, ← Real.rpow_mul (hQ i)]
        congr 1 <;> congr 1 <;> ring
  have hbound : Real.sqrt R ≤
      R ^ (1 / (2 * q)) * ∑ i, Q i ^ (1 / (2 * p)) := by
    calc
      Real.sqrt R ≤ ∑ i, Real.sqrt (Tr (H ∘ₗ coefficientDensity (C i))).re := hstart
      _ ≤ ∑ i, R ^ (1 / (2 * q)) * Q i ^ (1 / (2 * p)) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = _ := (Finset.mul_sum _ _ _).symm
  change R ^ (1 / (2 * p)) ≤ ∑ i, Q i ^ (1 / (2 * p))
  rcases eq_or_lt_of_le hR with hRzero | hRpos
  · rw [← hRzero, Real.zero_rpow (by positivity : (1 : ℝ) / (2 * p) ≠ 0)]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hQ i) _
  · have hfact : Real.sqrt R = R ^ (1 / (2 * q)) * R ^ (1 / (2 * p)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hRpos]
      congr 1
      have hconj : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
      calc
        (1 : ℝ) / 2 = (1 / q + 1 / p) / 2 := by rw [add_comm, hconj]
        _ = 1 / (2 * q) + 1 / (2 * p) := by ring
    rw [hfact] at hbound
    exact le_of_mul_le_mul_left hbound (Real.rpow_pos_of_pos hRpos _)

/-- The paper's quasi-entropy triangle, in the actual upstream definition of
sandwiched quasi-relative entropy. All coefficient maps use a common environment;
no normalization or strict positivity is required for this matrix-formula identity.
Support conventions for divergence are handled separately. -/
theorem sandwichedQuasi_coefficient_triangle {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (σ : L F) (C : ι → E →ₗ[ℂ] F) :
    (sandwichedQuasi p (coefficientDensity (∑ i, C i)) σ).re ^ (1 / (2 * p)) ≤
      ∑ i, (sandwichedQuasi p (coefficientDensity (C i)) σ).re ^ (1 / (2 * p)) := by
  let S : L F := CFC.rpow σ ((1 - p) / (2 * p))
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hD (D : E →ₗ[ℂ] F) :
      coefficientDensity (S ∘ₗ D) = S * coefficientDensity D * S := by
    simp only [coefficientDensity, LinearMap.adjoint_comp, hS.adjoint_eq]
    rfl
  have h := schatten_coefficient_triangle hp (fun i => S ∘ₗ C i)
  have hsum : (∑ i, S ∘ₗ C i) = S ∘ₗ ∑ i, C i := by
    ext v
    simp
  rw [hsum] at h
  simp only [hD] at h
  exact h

/-- Finite-dimensional spectra are finite even over the real scalar field. -/
theorem finite_real_operator_spectrum (X : L F) : (spectrum ℝ X).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum X).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- The product law for powers whose total exponent is nonzero. Finite spectrum
makes negative powers continuous on the spectrum even at a singular operator. -/
theorem operator_rpow_mul (X : L F) (hX : X.IsPositive) (a b : ℝ)
    (hab : a + b ≠ 0) :
    CFC.rpow X a * CFC.rpow X b = CFC.rpow X (a + b) := by
  have hX0 : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2 hX
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hX0]
  rw [← cfc_mul _ _ X ((finite_real_operator_spectrum X).continuousOn _)
    ((finite_real_operator_spectrum X).continuousOn _)]
  apply cfc_congr
  intro t ht
  exact (Real.rpow_add' (spectrum_nonneg_of_nonneg hX0 ht) hab).symm

/-- Homogeneity of positive operator powers, including singular operators. -/
theorem operator_rpow_smul (X : L F) (hX : X.IsPositive) {c : ℝ} (hc : 0 ≤ c)
    (a : ℝ) : CFC.rpow (c • X) a = c ^ a • CFC.rpow X a := by
  have hX0 : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2 hX
  have hcX : 0 ≤ c • X := smul_nonneg hc hX0
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hcX, CFC.rpow_eq_cfc_real hX0]
  rw [← cfc_comp_smul c (fun t : ℝ => t ^ a) X
    (((finite_real_operator_spectrum X).image (fun t => c • t)).continuousOn _)
    hX.isSelfAdjoint]
  rw [← cfc_smul (c ^ a) (fun t : ℝ => t ^ a) X
    ((finite_real_operator_spectrum X).continuousOn _)]
  apply cfc_congr
  intro t ht
  exact Real.mul_rpow hc (spectrum_nonneg_of_nonneg hX0 ht)

/-- A positive power times its inverse is a contraction, including on the
kernel where both factors vanish. -/
theorem operator_rpow_mul_neg_le_one (X : L F) (hX : X.IsPositive)
    {a : ℝ} (ha : a ≠ 0) :
    CFC.rpow X a * CFC.rpow X (-a) ≤ 1 := by
  have hX0 : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2 hX
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hX0]
  rw [← cfc_mul _ _ X ((finite_real_operator_spectrum X).continuousOn _)
    ((finite_real_operator_spectrum X).continuousOn _)]
  rw [← cfc_const_one ℝ X]
  apply cfc_mono (hf := (finite_real_operator_spectrum X).continuousOn _)
    (hg := (finite_real_operator_spectrum X).continuousOn _)
  intro t ht
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg hX0 ht) with ht0 | htpos
  · simp [← ht0, Real.zero_rpow ha, Real.zero_rpow (neg_ne_zero.mpr ha)]
  · rw [← Real.rpow_add htpos, add_neg_cancel, Real.rpow_zero]

/-- Positive operator products have nonnegative real trace, even when they do
not commute. -/
theorem trace_mul_re_nonneg (X Y : L F) (hX : X.IsPositive) (hY : Y.IsPositive) :
    0 ≤ (Tr (X * Y)).re := by
  change 0 ≤ (Tr (X ∘ₗ Y)).re
  rw [trace_comp_eq_double_sum_eigen_overlap X Y hX hY]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (hY.nonneg_eigenvalues (hn := rfl) j)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hX.nonneg_eigenvalues (hn := rfl) i) (Complex.normSq_nonneg _)

/-- Multiplication by a positive weight preserves the real trace order. -/
theorem trace_mul_re_mono {A B : L F} (hAB : A ≤ B) (X : L F) (hX : X.IsPositive) :
    (Tr (A * X)).re ≤ (Tr (B * X)).re := by
  have h := trace_mul_re_nonneg (B - A) X
    ((LinearMap.nonneg_iff_isPositive _).1 (sub_nonneg.mpr hAB)) hX
  simpa only [sub_mul, map_sub, Complex.sub_re, sub_nonneg] using h

/-- The trace-power domination estimate used in the quasi-entropy bound. -/
theorem trace_rpow_le_weighted_trace {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (X Y : L F) (hX : X.IsPositive) (hY : Y.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) (hXY : X ≤ c • Y) :
    (Tr (CFC.rpow X p)).re ≤ c ^ (p - 1) * (Tr (CFC.rpow Y (p - 1) * X)).re := by
  have hord : CFC.rpow X (p - 1) ≤ CFC.rpow (c • Y) (p - 1) :=
    CFC.rpow_le_rpow (by constructor <;> linarith) hXY
  rw [operator_rpow_smul Y hY hc] at hord
  have ht := trace_mul_re_mono hord X hX
  rw [rpow_sub_one_mul_self X hX hp] at ht
  simpa only [smul_mul_assoc, LinearMap.map_smul_of_tower, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ht

/-- The paper's unnormalized quasi-entropy bound for the entire interval
`1 < p ≤ 2`, including singular reference operators and the zero input.
The proof uses operator monotonicity of the `(p-1)` power and finite-spectrum
functional calculus, so it needs no separate max-relative-entropy theorem. -/
theorem sandwichedQuasi_le_of_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (ρ σ : L F) (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) (hdom : ρ ≤ c • σ) :
    (sandwichedQuasi p ρ σ).re ≤ c ^ (p - 1) * (Tr ρ).re := by
  let s : ℝ := (p - 1) / p
  let a : ℝ := -(s / 2)
  let S : L F := CFC.rpow σ a
  let X : L F := S * ρ * S
  let Y : L F := CFC.rpow σ (1 / p)
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < s := div_pos (by linarith) hp0
  have hs1 : s < 1 := (div_lt_one hp0).2 (by linarith)
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hX : X.IsPositive := by
    have h := hρ.conj_adjoint S
    simpa only [hS.adjoint_eq] using h
  have hY : Y.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hexp : a + 1 + a = 1 / p := by
    dsimp [a, s]
    field_simp
    ring
  have hSσS : S * σ * S = Y := by
    have hσpow : σ = CFC.rpow σ 1 :=
      (CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).2 hσ)).symm
    calc
      S * σ * S = CFC.rpow σ a * CFC.rpow σ 1 * CFC.rpow σ a := by rw [← hσpow]
      _ = CFC.rpow σ (a + 1) * CFC.rpow σ a := by
        rw [operator_rpow_mul σ hσ a 1 (by dsimp [a]; linarith)]
      _ = CFC.rpow σ (a + 1 + a) :=
        operator_rpow_mul σ hσ _ _ (by rw [hexp]; positivity)
      _ = Y := by rw [hexp]
  have hXY : X ≤ c • Y := by
    have h := hS.isSelfAdjoint.conjugate_le_conjugate hdom
    simpa only [mul_smul_comm, smul_mul_assoc, hSσS] using h
  have hYpow : CFC.rpow Y (p - 1) = CFC.rpow σ s := by
    dsimp only [Y]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg σ (1 / p) (p - 1)
      (by positivity) (by linarith) ((LinearMap.nonneg_iff_isPositive _).2 hσ)]
    congr 1
    dsimp [s]
    ring
  have hcontraction : S * CFC.rpow σ s * S ≤ 1 := by
    have has : a + s = s / 2 := by dsimp [a]; ring
    change CFC.rpow σ a * CFC.rpow σ s * CFC.rpow σ a ≤ 1
    rw [operator_rpow_mul σ hσ a s (by rw [has]; positivity), has]
    exact operator_rpow_mul_neg_le_one σ hσ (by positivity : s / 2 ≠ 0)
  have htrace : Tr (CFC.rpow σ s * X) = Tr ((S * CFC.rpow σ s * S) * ρ) := by
    calc
      Tr (CFC.rpow σ s * X) = Tr ((CFC.rpow σ s * S * ρ) * S) := by simp only [X, mul_assoc]
      _ = Tr (S * (CFC.rpow σ s * S * ρ)) := LinearMap.trace_mul_comm ℂ _ _
      _ = Tr ((S * CFC.rpow σ s * S) * ρ) := by simp only [mul_assoc]
  have htracele : (Tr (CFC.rpow σ s * X)).re ≤ (Tr ρ).re := by
    rw [htrace]
    simpa only [one_mul] using trace_mul_re_mono hcontraction ρ hρ
  have ht := trace_rpow_le_weighted_trace hp hp2 X Y hX hY hc hXY
  rw [hYpow] at ht
  have hfinal := ht.trans (mul_le_mul_of_nonneg_left htracele (Real.rpow_nonneg hc _))
  have hexp' : (1 - p) / (2 * p) = a := by dsimp [a, s]; ring
  unfold sandwichedQuasi
  rw [hexp']
  exact hfinal

/-- One-shot decomposition bound, obtained from the proved rectangular Schatten
triangle and the proved quasi-entropy domination bound. The hypotheses are only
concrete positive-operator domination and trace bounds for the component maps. -/
theorem sandwichedQuasi_decomposition_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (σ : L F) (hσ : σ.IsPositive)
    (C : ι → E →ₗ[ℂ] F) (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, coefficientDensity (C i) ≤ lam i • σ)
    (htrace : ∀ i, (Tr (coefficientDensity (C i))).re ≤ b i ^ 2) :
    (sandwichedQuasi p (coefficientDensity (∑ i, C i)) σ).re ^ (1 / (2 * p)) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  refine (sandwichedQuasi_coefficient_triangle hp σ C).trans ?_
  apply Finset.sum_le_sum
  intro i _
  have hq := sandwichedQuasi_le_of_le hp hp2 (coefficientDensity (C i)) σ
    (coefficientDensity_pos _) hσ (hlam i) (hdom i)
  have hq0 : 0 ≤ (sandwichedQuasi p (coefficientDensity (C i)) σ).re :=
    trace_rpow_re_nonneg _ p
  have hbound := hq.trans (mul_le_mul_of_nonneg_left (htrace i)
    (Real.rpow_nonneg (hlam i) _))
  calc
    (sandwichedQuasi p (coefficientDensity (C i)) σ).re ^ (1 / (2 * p)) ≤
        (lam i ^ (p - 1) * b i ^ 2) ^ (1 / (2 * p)) :=
      Real.rpow_le_rpow hq0 hbound (by positivity)
    _ = b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (hlam i) _) (sq_nonneg _),
        ← Real.rpow_mul (hlam i), ← Real.rpow_two, ← Real.rpow_mul (hb i)]
      have hexp : (2 : ℝ) * (1 / (2 * p)) = 1 / p := by ring
      rw [hexp, show (p - 1) * (1 / (2 * p)) = (p - 1) / (2 * p) by ring]
      exact mul_comm _ _



/-- The coefficient map of a bipartite vector in a fixed environmental basis.
This is an actual linear equivalence, so decomposing vectors decomposes their
coefficient maps while preserving every cross term. -/
noncomputable def vectorCoefficient : (F ⊗[ℂ] E) ≃ₗ[ℂ] (E →ₗ[ℂ] F) :=
  (vecLinearEquiv (ℋ₁ := F) (stdOrthonormalBasis ℂ E).toBasis).symm

theorem vec_vectorCoefficient (v : F ⊗[ℂ] E) :
    vec (stdOrthonormalBasis ℂ E).toBasis (vectorCoefficient v) = v := by
  rw [← vecLinearEquiv_toLinearMap]
  exact LinearEquiv.apply_symm_apply _ _

/-- Columns of the coefficient map are exactly the environmental slices. -/
theorem vectorCoefficient_apply_basis (v : F ⊗[ℂ] E)
    (j : Fin (Module.finrank ℂ E)) :
    vectorCoefficient v (stdOrthonormalBasis ℂ E j) =
      tensorRightSlice (stdOrthonormalBasis ℂ E) j v := by
  have h := congrArg (tensorRightSlice (stdOrthonormalBasis ℂ E) j)
    (vec_vectorCoefficient v)
  simpa [vec_apply, tensorRightSlice_tmul] using h

/-- The coefficient density equals the sum of outer products of its columns. -/
theorem coefficientDensity_eq_sum_outer (C : E →ₗ[ℂ] F) :
    coefficientDensity C = ∑ j, outer_product
      (C (stdOrthonormalBasis ℂ E j)) (C (stdOrthonormalBasis ℂ E j)) := by
  ext x
  change C (C.adjoint x) = _
  calc
    C (C.adjoint x) = C (∑ j, inner ℂ (stdOrthonormalBasis ℂ E j) (C.adjoint x) •
        stdOrthonormalBasis ℂ E j) :=
      congrArg C ((stdOrthonormalBasis ℂ E).sum_repr' _).symm
    _ = _ := by
      simp [map_sum, map_smul, LinearMap.adjoint_inner_right, LinearMap.sum_apply,
        outer_product_eq_rankOne]

/-- The manuscript's coefficient-matrix/partial-trace identity, on actual
bipartite vectors and actual partial trace. -/
theorem coefficientDensity_vector (v : F ⊗[ℂ] E) :
    coefficientDensity (vectorCoefficient v) = TrRight (outer_product v v) := by
  rw [coefficientDensity_eq_sum_outer,
    TrRight_outer_product (stdOrthonormalBasis ℂ E)]
  simp_rw [vectorCoefficient_apply_basis]

/-- The unnormalized output trace is the squared norm of its purification. -/
theorem trace_coefficientDensity_vector (v : F ⊗[ℂ] E) :
    (Tr (coefficientDensity (vectorCoefficient v))).re = ‖v‖ ^ 2 := by
  rw [coefficientDensity, ← LinearMap.trace_comp_comm' _ _,
    ← inner_vec_eq_trace (stdOrthonormalBasis ℂ E), vec_vectorCoefficient]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

/-- Schatten decomposition bound for actual bipartite output vectors. -/
theorem sandwichedQuasi_vector_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (σ : L F) (hσ : σ.IsPositive)
    (v : ι → F ⊗[ℂ] E) (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, TrRight (outer_product (v i) (v i)) ≤ lam i • σ)
    (hnorm : ∀ i, ‖v i‖ ≤ b i) :
    (sandwichedQuasi p (TrRight (outer_product (∑ i, v i) (∑ i, v i))) σ).re ^
        (1 / (2 * p)) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  have h := sandwichedQuasi_decomposition_bound hp hp2 σ hσ
    (fun i => vectorCoefficient (v i)) b lam hb hlam
    (fun i => by rw [coefficientDensity_vector]; exact hdom i)
    (fun i => by
      rw [trace_coefficientDensity_vector]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm i) 2)
  rw [← map_sum] at h
  simpa only [coefficientDensity_vector] using h

/-- Direct application to a finite family of dilation operators on one pure
input. The trace bounds are derived from their actual operator norms. -/
theorem sandwichedQuasi_dilation_bound {A : Type*} [Qudit A]
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (σ : L F) (hσ : σ.IsPositive) (U : ι → A →ₗ[ℂ] F ⊗[ℂ] E)
    (ψ : A) (hψ : ‖ψ‖ = 1) (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, TrRight (krausTerm (U i) (outer_product ψ ψ)) ≤ lam i • σ)
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    (sandwichedQuasi p
      (TrRight (krausTerm (∑ i, U i) (outer_product ψ ψ))) σ).re ^ (1 / (2 * p)) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  have h := sandwichedQuasi_vector_bound hp hp2 σ hσ (fun i => U i ψ) b lam hb hlam
    (fun i => by simpa only [krausTerm, LinearMap.coe_mk, AddHom.coe_mk,
      comp_outer_product_adjoint] using hdom i)
    (fun i => by
      calc
        ‖U i ψ‖ ≤ ‖(U i).toContinuousLinearMap‖ * ‖ψ‖ :=
          (U i).toContinuousLinearMap.le_opNorm ψ
        _ ≤ b i := by simpa only [hψ, mul_one] using hnorm i)
  simpa only [krausTerm, LinearMap.coe_mk, AddHom.coe_mk,
    comp_outer_product_adjoint, LinearMap.sum_apply] using h

/-- Component domination puts every coefficient range in the support of `σ`.
The conclusion is stated as kernel inclusion, so it also covers zero-dimensional
spaces without an auxiliary nontriviality assumption. -/
theorem coefficientDensity_sum_support {ι : Type*} [Fintype ι]
    (σ : L F) (C : ι → E →ₗ[ℂ] F) (lam : ι → ℝ)
    (hdom : ∀ i, coefficientDensity (C i) ≤ lam i • σ) :
    LinearMap.ker σ ≤ LinearMap.ker (coefficientDensity (∑ i, C i)) := by
  intro x hx
  have hx0 : σ x = 0 := hx
  have hi : ∀ i, (C i).adjoint x = 0 := by
    intro i
    have hpos := (LinearMap.nonneg_iff_isPositive _).1 (sub_nonneg.mpr (hdom i))
    have hinner := hpos.re_inner_nonneg_right x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hx0, smul_zero,
      zero_sub, inner_neg_right, map_neg, coefficientDensity, LinearMap.comp_apply] at hinner
    rw [← LinearMap.adjoint_inner_left (C i) ((C i).adjoint x) x,
      inner_self_eq_norm_sq (𝕜 := ℂ)] at hinner
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((C i).adjoint x)]
  have hsum : (∑ i, C i).adjoint x = 0 := by
    simp only [map_sum, LinearMap.sum_apply, hi, Finset.sum_const_zero]
  change (∑ i, C i) ((∑ i, C i).adjoint x) = 0
  rw [hsum, map_zero]

end CoefficientMaps

section ChannelLift

universe uChannel
variable {A B E : Type uChannel} [Qudit A] [Qudit B] [Qudit E]

/-- Complete-positive domination implies ordinary positive-operator domination
on every positive input. -/
theorem CPLe.apply_nonneg {Φ Ψ : QuantumChannel.T A B} (h : CPLe Φ Ψ)
    {ρ : L A} (hρ : 0 ≤ ρ) : Φ ρ ≤ Ψ ρ := by
  have hp := completelyPositive_to_positiveMap (Ψ - Φ) h ρ hρ
  simpa only [LinearMap.sub_apply, sub_nonneg] using hp



end ChannelLift

end QuantumChannelContinuity


