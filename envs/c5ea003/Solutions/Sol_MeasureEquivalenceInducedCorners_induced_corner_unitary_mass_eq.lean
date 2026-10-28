-- Prove2me | solution 1 for MeasureEquivalenceInducedCorners.induced_corner_unitary_mass_eq
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:35:36.470485+00:00
-- url     : https://prove2.me/submissions/42170d51-d7c4-4682-bf9d-9eceab264a7e

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_L2CountCoefficients
import Definitions.Def_BenchmarkOperator20261026_L2CountInjections
import Definitions.Def_BenchmarkOperator20261026_L2FiniteOnes
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_MeasureEquivalenceL2Transport_twisted_coefficient_constant_norm_eq_adjoint

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

-- Preserved source skeleton: InducedCornerUnitary
section
/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

open MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]







omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem inducedShiftUnitary_coe (A : Set Z) (h : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedShiftUnitary μ A h u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => u (indexShift h⁻¹ p)) :=
  Lp.coeFn_compMeasurePreserving u (indexShift_preserving μ A h⁻¹)







variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)



end
end MeasureEquivalenceInducedCorners

end

-- Preserved source skeleton: L2MatrixColumns
section
/-! The column norm identities of a genuine isometry on the actual
product L2 space, without an assumed pointwise matrix or semifinite trace. -/

open MeasureTheory
open scoped ENNReal

namespace MeasureEquivalenceL2Coefficients

variable {X Y D : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Y) [SigmaFinite ν]

theorem unitary_column_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (e : D) (f : Lp ℂ 2 μ) :
    (∑' d, ‖matrixCoefficient μ ν U.toContinuousLinearEquiv.toContinuousLinearMap d e f‖ ^ 2) =
      ‖f‖ ^ 2 := by
  change (∑' d, ‖coefficient ν d (U (injection μ e f))‖ ^ 2) = ‖f‖ ^ 2
  rw [← norm_sq_eq_tsum_coefficient_norm_sq, U.norm_map, injection_norm]

theorem unitary_inverse_column_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d : D) (f : Lp ℂ 2 ν) :
    (∑' e, ‖matrixCoefficient ν μ U.symm.toContinuousLinearEquiv.toContinuousLinearMap e d f‖ ^ 2) =
      ‖f‖ ^ 2 :=
  unitary_column_norm_sq ν μ U.symm d f

end MeasureEquivalenceL2Coefficients

end

-- Preserved source skeleton: L2CountAdjoints
section
/-! Actual adjoint identities for the coordinate injections and
coefficients, and adjoint transposition of genuine operator matrices. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

theorem inner_injection_coefficient (d : D) (f : Lp ℂ 2 μ)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    inner ℂ (injection μ d f) u = inner ℂ f (coefficient μ d u) := by
  classical
  have hI := L2.integrable_inner (𝕜 := ℂ) (injection μ d f) u
  have hterm (i : D) :
      (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) =
        if i = d then inner ℂ f (coefficient μ d u) else 0 := by
    by_cases hi : i = d
    · subst i
      rw [if_pos rfl, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) d,
        coefficient_coe μ d u] with x hinj hc
      rw [hinj, hc]
      simp [injectionFun]
    · rw [if_neg hi]
      calc
        (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) = ∫ _ : X, (0 : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) i] with x hinj
          rw [hinj]
          simp [injectionFun, hi]
        _ = 0 := integral_zero _ _
  calc
    inner ℂ (injection μ d f) u =
        ∑' i : D, ∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ := by
      rw [L2.inner_def, integral_prod_symm _ hI, integral_countable hI.integral_prod_right]
      simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    _ = ∑' i : D, if i = d then inner ℂ f (coefficient μ d u) else 0 := tsum_congr hterm
    _ = inner ℂ f (coefficient μ d u) := by simp

theorem coefficient_adjoint (d : D) :
    (coefficientCLM μ d).adjoint = (injectionLI μ d).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact fun f u => inner_injection_coefficient μ d f u

theorem injection_adjoint (d : D) :
    (injectionLI μ d).toContinuousLinearMap.adjoint = coefficientCLM μ d := by
  rw [← coefficient_adjoint, ContinuousLinearMap.adjoint_adjoint]

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

/-- The genuine operator coefficient matrix transposes under adjoint. -/
theorem matrixCoefficient_adjoint
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d e : D) :
    (matrixCoefficient μ ν T d e).adjoint = matrixCoefficient ν μ T.adjoint e d := by
  simp only [matrixCoefficient, ContinuousLinearMap.adjoint_comp, injection_adjoint,
    coefficient_adjoint, ContinuousLinearMap.comp_assoc]

/-- Rows of the actual unitary coefficient matrix satisfy the dual
Parseval identity; no separately assumed row-mass premise is used. -/
theorem unitary_row_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d : D) (f : Lp ℂ 2 ν) :
    (∑' e, ‖(matrixCoefficient μ ν U.toContinuousLinearEquiv.toContinuousLinearMap d e).adjoint f‖ ^ 2) =
      ‖f‖ ^ 2 := by
  simp_rw [matrixCoefficient_adjoint]
  have hAdj : U.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap := U.adjoint_eq_symm
  rw [hAdj]
  exact unitary_inverse_column_norm_sq μ ν U d f

end MeasureEquivalenceL2Coefficients

end

-- Preserved source skeleton: L2FiniteOnes
section
/-! Canonical indicator vectors for finite sets, including their exact
mass, restriction and zero-extension identities. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)







theorem restrictedOne_coe (A : Set X) (hfin : μ A ≠ ∞) :
    restrictedOne μ A hfin =ᵐ[μ.restrict A] fun _ => (1 : ℂ) := by
  simpa only [Set.indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := by simpa using hfin) (c := (1 : ℂ)))

theorem restrictedOne_norm_sq (A : Set X) (hfin : μ A ≠ ∞) :
    ‖restrictedOne μ A hfin‖ ^ 2 = μ.real A := by
  rw [l2_norm_sq_integral]
  calc
    (∫ x, ‖restrictedOne μ A hfin x‖ ^ 2 ∂μ.restrict A) = ∫ _ : X, (1 : ℝ) ∂μ.restrict A := by
      apply integral_congr_ae
      filter_upwards [restrictedOne_coe μ A hfin] with x hx
      simp [hx]
    _ = μ.real A := by simp [measureReal_def]







end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: L2MatrixProjection
section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X Y D Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D] [MeasurableSpace Z]
  (μ : Measure X) [SigmaFinite μ]

theorem coefficient_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    coefficient μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
      indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u) := by
  apply Lp.ext
  filter_upwards [coefficient_coe μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u),
    ae_slice_of_ae μ (indicatorL2_coe (μ.prod Measure.count) (hq hs) u) d,
    indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u),
    coefficient_coe μ d u] with x hc hi ho hu
  rw [hc, hi, ho]
  by_cases hx : q (x,d) ∈ s <;> simp [hx, hu]

theorem injection_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D) (u : Lp ℂ 2 μ) :
    injection μ d (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u) =
      indicatorL2 (μ.prod Measure.count) (hq hs) (injection μ d u) := by
  classical
  apply Lp.ext
  filter_upwards [injection_coe μ d
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u),
    indicatorL2_coe (μ.prod Measure.count) (hq hs) (injection μ d u), injection_coe μ d u,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (Measure.count : Measure D))).ae
      (indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u)]
      with p hleft hright hinj hbase
  rw [hleft, hright]
  simp only [Set.indicator_apply]
  rw [hinj]
  by_cases hd : p.2 = d
  · have hp' : p = (p.1, d) := Prod.ext rfl hd
    rw [hp'] at *
    simp only [injectionFun, if_pos rfl]
    rw [hbase]
    by_cases hp : q (p.1, d) ∈ s
    · simp [hp]
    · simp [hp]
  · by_cases hp : q p ∈ s <;> simp [injectionFun, hd, hp]

variable (ν : Measure Y) [SigmaFinite ν]

/-- Matrix coefficients of an actual intertwiner satisfy the twisted
measurable-projection relation on their source and target slices. -/
theorem matrixCoefficient_intertwines_projections
    (q : X × D → Z) (r : Y × D → Z) (hq : Measurable q) (hr : Measurable r)
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D)))
    (hT : ∀ (s : Set Z) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))),
      T (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
        indicatorL2 (ν.prod Measure.count) (hr hs) (T u))
    (s : Set Z) (hs : MeasurableSet s) (d e : D) (u : Lp ℂ 2 μ) :
    matrixCoefficient μ ν T d e
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u) =
        indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
          (matrixCoefficient μ ν T d e u) := by
  change coefficient ν d (T (injection μ e
    (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u))) =
      indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
        (coefficient ν d (T (injection μ e u)))
  rw [injection_indicator μ q hq s hs e u, hT s hs, coefficient_indicator ν r hr s hs d]

end MeasureEquivalenceL2Coefficients

end

-- Preserved source skeleton: L2IndexShiftCoefficients
section
/-! Actual matrix-coefficient covariance follows directly from a genuine
intertwiner of the left counting-coordinate shifts. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 800000

namespace MeasureEquivalenceL2Coefficients

open MeasureEquivalenceInducedCorners MeasureUnitary

noncomputable section

variable {X G : Type*} [MeasurableSpace X] [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SigmaFinite μ]

theorem coefficient_inducedShift (A : Set X) (g d : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    coefficient (μ.restrict A) d (inducedShiftUnitary μ A g u) =
      coefficient (μ.restrict A) (g⁻¹*d) u := by
  apply Lp.ext
  filter_upwards [coefficient_coe (μ.restrict A) d (inducedShiftUnitary μ A g u),
    ae_slice_of_ae (μ.restrict A) (inducedShiftUnitary_coe μ A g u) d,
    coefficient_coe (μ.restrict A) (g⁻¹*d) u] with x hc hs hu
  exact hc.trans (hs.trans hu.symm)

theorem inducedShift_injection (A : Set X) (g e : G) (f : Lp ℂ 2 (μ.restrict A)) :
    inducedShiftUnitary μ A g (injection (μ.restrict A) e f) =
      injection (μ.restrict A) (g*e) f := by
  classical
  apply coefficient_ext (μ.restrict A)
  intro d
  rw [coefficient_inducedShift]
  simp only [coefficient_injection]
  have he : g⁻¹*d = e ↔ d = g*e := by
    constructor
    · intro h
      rw [← h, mul_inv_cancel_left]
    · rintro rfl
      exact inv_mul_cancel_left g e
  exact if_congr he rfl rfl

theorem matrixCoefficient_shift_covariance (A B : Set X)
    (T : Lp ℂ 2 (cornerMeasure (G := G) μ A) →L[ℂ]
      Lp ℂ 2 (cornerMeasure (G := G) μ B))
    (hT : ∀ (g : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      T (inducedShiftUnitary μ A g u) = inducedShiftUnitary μ B g (T u))
    (g d e : G) :
    matrixCoefficient (μ.restrict A) (μ.restrict B) T (g*d) (g*e) =
      matrixCoefficient (μ.restrict A) (μ.restrict B) T d e := by
  apply ContinuousLinearMap.ext
  intro f
  change coefficient (μ.restrict B) (g*d) (T (injection (μ.restrict A) (g*e) f)) = _
  rw [← inducedShift_injection μ A g e f, hT,
    coefficient_inducedShift, inv_mul_cancel_left]
  rfl

end
end MeasureEquivalenceL2Coefficients

end

/-! A genuine unitary equivalence of induced corner modules preserves
their finite base measures. All coefficients, adjoints and Parseval
sums are those of the given unitary; no matrix field or trace is assumed. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
open MeasureEquivalenceInducedCorners
open MeasureUnitary MeasureEquivalenceL2Restriction
  MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Transport
variable {X G : Type*} [MeasurableSpace X] [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)

include hmp

theorem solution
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (U : Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := G) μ B))
    (hproj : ∀ (s : Set X) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (indicatorL2 (cornerMeasure μ A) (hs.preimage orbitPoint_measurable) u) =
        indicatorL2 (cornerMeasure μ B) (hs.preimage orbitPoint_measurable) (U u))
    (hshift : ∀ (g : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (inducedShiftUnitary μ A g u) = inducedShiftUnitary μ B g (U u)) :
    μ A = μ B := by
  let T := U.toContinuousLinearEquiv.toContinuousLinearMap
  have hentry (d e : G) :
      ‖matrixCoefficient (μ.restrict A) (μ.restrict B) T d e
          (restrictedOne μ A hfinA)‖ =
        ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T d e).adjoint
          (restrictedOne μ B hfinB)‖ := by
    apply twisted_coefficient_constant_norm_eq_adjoint μ
      (MeasurableEquiv.smul d) (MeasurableEquiv.smul e) (hmp d) (hmp e)
      A B hA hB hfinA hfinB
    intro s hs f
    exact matrixCoefficient_intertwines_projections (μ.restrict A) (μ.restrict B)
      orbitPoint orbitPoint orbitPoint_measurable orbitPoint_measurable T hproj s hs d e f
  have hcov (d : G) :
      matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1 =
        matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 d⁻¹ := by
    have h := matrixCoefficient_shift_covariance μ A B T hshift d⁻¹ d 1
    simpa only [inv_mul_cancel, mul_one] using h.symm
  have hreal : μ.real A = μ.real B := by
    calc
      μ.real A = ‖restrictedOne μ A hfinA‖ ^ 2 := (restrictedOne_norm_sq μ A hfinA).symm
      _ = ∑' d : G, ‖matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1
          (restrictedOne μ A hfinA)‖ ^ 2 :=
        (unitary_column_norm_sq (μ.restrict A) (μ.restrict B) U 1 _).symm
      _ = ∑' d : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 := tsum_congr (fun d => by rw [hentry d 1])
      _ = ∑' d : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 d⁻¹).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 := tsum_congr (fun d => by rw [hcov d])
      _ = ∑' e : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 e).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 :=
        (Equiv.inv G).tsum_eq (fun e : G =>
          ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 e).adjoint
            (restrictedOne μ B hfinB)‖ ^ 2)
      _ = ‖restrictedOne μ B hfinB‖ ^ 2 := unitary_row_norm_sq (μ.restrict A) (μ.restrict B) U 1 _
      _ = μ.real B := restrictedOne_norm_sq μ B hfinB
  exact (ENNReal.toReal_eq_toReal_iff' hfinA hfinB).mp hreal
