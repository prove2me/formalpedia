-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.357811+00:00
-- url     : https://prove2.me/submissions/7a253fd7-a57d-4510-9e6b-f5bd2f82fcd1

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ReducedResidueCofinalTransference
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenUniformity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Theorems.Thm_Wikipedia_SzemeredisTheorem_CutDiscrepancyLe_hasConvolutionMomentBound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_abs_cutCorrelation_pow_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_centeredAbsoluteMean_le_mean_add_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cutDiscrepancy_model_of_monomialCorrelationBound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_testMonomial_generalizedConvolution
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_sum_fin_succ
import Theorems.Thm_Wikipedia_SzemeredisTheorem_relativeAPCount_lower_bound_of_model

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem













theorem wTrickedPrimeWeight_nonneg {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedPrimeWeight
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg hα
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h.2.ne_zero)))
  · exact le_rfl













end Wikipedia.SzemeredisTheorem

end

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





















































theorem mean_sum_fin_of_pos
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i)) = mean h := by
  cases r with
  | zero => simp at hr
  | succ n => exact mean_sum_fin_succ n h

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

theorem cutCorrelation_one_eq_mean_sub
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean f - mean g := by
  calc
    cutCorrelation r f g
        (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
      mean (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) :=
      cutCorrelation_one r f g
    _ = mean (fun z : G => f z - g z) :=
      mean_sum_fin_of_pos hr (fun z => f z - g z)
    _ = mean f - mean g := mean_sub f g

/-- The constant-one tests show that cut discrepancy controls the difference
of the means whenever at least one coordinate is present. -/
theorem CutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hr : 0 < r) :
    |mean f - mean g| ≤ ε := by
  have hone := h
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
    (fun _ _ => by norm_num) (fun _ _ => le_rfl)
  simpa [cutCorrelation_one_eq_mean_sub hr f g] using hone

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl































































end Wikipedia.SzemeredisTheorem

end

section



/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









































theorem IsBoundedCutTest.isAbsBounded
    {G : Type*} {n : ℕ} {u : CutTestFamily G n}
    (hu : IsBoundedCutTest u) :
    IsAbsBoundedCutTest u := by
  intro i x
  rw [abs_of_nonneg (hu.nonneg i x)]
  exact hu.le_one i x



























end Wikipedia.SzemeredisTheorem

end

section



/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/













/-! ## Boolean cut coordinates -/







theorem cutTestFamilyOfBooleanAssignment_bounded
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    IsBoundedCutTest (cutTestFamilyOfBooleanAssignment b) := by
  constructor <;> intro i y <;>
    unfold cutTestFamilyOfBooleanAssignment booleanValue <;>
    split <;> norm_num













/-! ## The finite dense-model test family -/















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Moments of generalized convolutions

Products of generalized convolutions are averages over independent copies of
the corresponding sum fibers.  This file records that disintegration
exactly and packages the remaining analytic estimate as a concrete moment
condition.  It is the interface at which iterated Cauchy--Schwarz and the
linear-forms estimate enter the dense-model proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial











/-- A moment estimate for arbitrary bounded cut tests specializes to the
Boolean moment estimate. -/
theorem HasConvolutionMomentBound.toBoolean
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasConvolutionMomentBound r d ν η) :
    HasBooleanConvolutionMomentBound r d ν η := by
  intro n hn b
  exact h n hn
    (fun a => cutTestFamilyOfBooleanAssignment (b a))
    (fun a => cutTestFamilyOfBooleanAssignment_bounded (b a))

/-- Boolean expanded moments are precisely the monomial correlations of the
Boolean generalized-convolution family. -/
theorem hasMonomialCorrelationBound_booleanCutConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasBooleanConvolutionMomentBound r d ν η) :
    HasMonomialCorrelationBound
      (booleanCutConvolution (G := G) (r + 1))
      ν d η := by
  intro n hn b
  change
    |finitePairing (ν - fun _ => 1)
      (testMonomial
        (fun t =>
          generalizedConvolution (r + 1)
            (cutTestFamilyOfBooleanAssignment t)) b)| ≤ η
  rw [finitePairing_testMonomial_generalizedConvolution
    r ν (fun t => cutTestFamilyOfBooleanAssignment t) b]
  exact h n hn b

/-- The arbitrary bounded moment condition supplies the monomial
correlation input of polynomial dense-model duality. -/
theorem HasConvolutionMomentBound.hasMonomialCorrelationBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasConvolutionMomentBound r d ν η) :
    HasMonomialCorrelationBound
      (booleanCutConvolution (G := G) (r + 1))
      ν d η :=
  hasMonomialCorrelationBound_booleanCutConvolution h.toBoolean

/-- Direct polynomial cut-dense-model consequence of the expanded
convolution moment condition. -/
theorem exists_cutDiscrepancy_model_of_convolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmoment :
      HasConvolutionMomentBound r p.natDegree ν η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe (r + 1) f g
        (polynomialCoefficientL1 p * η + δ * M) := by
  classical
  exact exists_cutDiscrepancy_model_of_monomialCorrelationBound
    (r + 1) (Nat.succ_pos r)
    hδ hη hM0 hf0 hfν hp hM
    hmoment.hasMonomialCorrelationBound

end Wikipedia.SzemeredisTheorem

end

section





/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators







































/-- Quantitative strong linear-forms conclusion in cut-discrepancy form.
The displayed power comparison is the explicit parameter conversion from
the linear-forms error to the requested cut error. -/
theorem HasLinearFormsCondition.cutDiscrepancyLe_one
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (h : HasLinearFormsCondition (n + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (hε : 0 ≤ ε)
    (hηε :
      (2 : ℝ) ^ (2 ^ (n + 1)) * η ≤
        ε ^ (2 ^ (n + 1))) :
    CutDiscrepancyLe (n + 1) ν (fun _ => 1) ε := by
  intro u hu0 hu1
  have hu : IsAbsBoundedCutTest u :=
    (show IsBoundedCutTest u from ⟨hu0, hu1⟩).isAbsBounded
  have hpow :
      |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
          (2 ^ (n + 1)) ≤
        ε ^ (2 ^ (n + 1)) :=
    (h.abs_cutCorrelation_pow_le hN u hu).trans hηε
  exact le_of_pow_le_pow_left₀
    (pow_ne_zero _ two_ne_zero) hε hpow

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

universe u



















/-! ## Finite convex mixtures -/



namespace ConvolutionMixture



















end ConvolutionMixture

/-! ## Consequences for dense-model moments -/





/-- For a nonnegative majorant, positive-arity cut discrepancy from one
also gives the absolute first-moment bound needed by polynomial
approximation. -/
theorem CutDiscrepancyLe.centeredAbsoluteMean_le_two_add
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe r ν (fun _ => 1) ε)
    (hr : 0 < r) (hν : ∀ x, 0 ≤ ν x) :
    centeredAbsoluteMean ν ≤ 2 + ε := by
  have hmeanAbs := hcut.abs_mean_sub_le hr
  have hmean : mean ν ≤ 1 + ε := by
    rw [mean_const] at hmeanAbs
    linarith [le_abs_self (mean ν - 1)]
  calc
    centeredAbsoluteMean ν ≤ mean ν + 1 :=
      centeredAbsoluteMean_le_mean_add_one hν
    _ ≤ 2 + ε := by linarith



/-- Direct quantitative dense-model theorem from the ordinary CFZ
linear-forms condition.  The output error displays separately the
polynomial-monomial loss and the positive-part approximation loss. -/
theorem exists_cutDiscrepancy_model_of_linearFormsCondition
    {r N : ℕ} [NeZero N]
    {f ν : ZMod N → ℝ}
    {linearFormsError cutError : ℝ}
    {p : ℝ[X]} {approximationError : ℝ}
    (happrox : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hν0 : ∀ x, 0 ≤ ν x)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1))) :
    ∃ g : ZMod N → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe (r + 1) f g
        (polynomialCoefficientL1 p * cutError +
          approximationError * (2 + cutError)) := by
  have hmajorantCut :
      CutDiscrepancyLe (r + 1) ν (fun _ => 1) cutError :=
    hLF.cutDiscrepancyLe_one hN hcutError hconvert
  exact
    exists_cutDiscrepancy_model_of_convolutionMomentBound
      r happrox hcutError (by positivity)
      hf0 hfν hp
      (hmajorantCut.centeredAbsoluteMean_le_two_add
        (Nat.succ_pos r) hν0)
      (hmajorantCut.hasConvolutionMomentBound p.natDegree)

end Wikipedia.SzemeredisTheorem

end

section




/-!
# Quantitative relative Szemerédi assembly

This file composes the parts of transference which do not depend on the
remaining sparse-simplex comparison.

* Cut discrepancy against the constant tests retains the mean of the sparse
  weight in its dense model.
* A uniform weighted Szemerédi theorem gives a positive lower bound for the
  dense model's progression count.
* Any quantitative relative-counting comparison then transfers that lower
  bound back to the sparse weight.

The final theorem plugs in the polynomial dense-model theorem obtained from
the ordinary CFZ linear-forms condition.  Its only unproved analytic input
is named explicitly by `RelativeAPComparisonLe`; no asymptotic or
pseudorandomness assertion is hidden in this module.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Polynomial









/-- End-to-end quantitative transference from the CFZ linear-forms
condition, a weighted dense Szemerédi bound, and the named relative
comparison input.

The progressions have length `r + 2`, so the dense model uses cut arity
`r + 1` and precisely the same `r + 2`-linear-forms condition. -/
theorem relativeAPCount_lower_bound_of_linearFormsCondition
    {r N : ℕ} [NeZero N]
    {ν f : ZMod N → ℝ}
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hν0 : ∀ x, 0 ≤ ν x)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hmean :
      δ + polynomialDenseModelError
          p cutError approximationError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe r N ν
        (polynomialDenseModelError
          p cutError approximationError)
        countError) :
    denseCount - countError ≤
      cyclicAPCount (r + 2) N f := by
  obtain ⟨g, hg, hcut⟩ :=
    exists_cutDiscrepancy_model_of_linearFormsCondition
      happroximationError hcutError
      hf0 hfν hν0 hp hLF hN hconvert
  exact relativeAPCount_lower_bound_of_model
    hweighted hf0 hfν hg hcut hmean hcomparison



end Wikipedia.SzemeredisTheorem

end
/-!
# Cofinal transference on reduced residue classes

The sieve normalization for the W-tricked majorant uses that the selected
shift is coprime to `W`.  The prime-density theorem already selects such a
shift, but the older cofinal interface retained only the weaker inequality
`b < W`.

There is a second quantifier-order issue.  Converting AP cut discrepancy to
simplex face-cut discrepancy requires

```
Nat.Coprime N (Nat.factorial (r + 1)).
```

This is available after the cofinal argument selects a sufficiently large
prime modulus, but need not hold eventually at every natural modulus.

This file records the corrected interface.  Reduced-residue membership is
preserved through density selection, and the relative-counting comparison
is supplied by a callback invoked only after the prime modulus and its
factorial-coprimality proof have been constructed.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped Polynomial

open Wikipedia.SzemeredisTheorem in
/-- Quantitative cofinal-prime transference with the two corrected
quantifier orders.

The majorization and linear-forms hypotheses are required only for reduced
residue classes.  The comparison callback is not assumed eventually at all
moduli: it is called at the selected prime modulus, after primality has
supplied coprimality with `(r + 1)!`. -/
theorem
    solution
    {r W : ℕ} {α : ℝ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (hα : 0 ≤ α)
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasUniformWeightedAPCount
        (r + 2) δ denseCount)
    (hν0 :
      ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x)
    (hmajor :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x)
    (hLF :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError)
    (hcomparison :
      ∀ M b,
        Nat.Coprime (M + 1) (Nat.factorial (r + 1)) →
        HasLinearFormsCondition
          (r + 2) (M + 1) (ν M b)
            linearFormsError →
        RelativeAPComparisonLe
          r (M + 1) (ν M b)
          (polynomialDenseModelError
            p cutError approximationError)
          countError) :
    CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
      (r + 2) α W
      (δ + polynomialDenseModelError
        p cutError approximationError)
      (denseCount - countError) := by
  have hall :
      ∀ᶠ M : ℕ in atTop,
        (∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x) ∧
        (∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError) :=
    hmajor.and hLF
  rw [eventually_atTop] at hall
  obtain ⟨Mthreshold, hfrom⟩ := hall
  intro M₀
  obtain ⟨q, hqLarge, hqPrime⟩ :=
    Nat.exists_infinite_primes
      (max (max M₀ Mthreshold) (r + 1) + 1)
  let M := q - 1
  have hMsucc : M + 1 = q := by
    dsimp [M]
    omega
  have hM₀ : M₀ ≤ M := by
    dsimp [M]
    omega
  have hMthreshold : Mthreshold ≤ M := by
    dsimp [M]
    omega
  have hrank : r + 1 < M + 1 := by
    dsimp [M]
    omega
  obtain ⟨hmajorM, hLFM⟩ :=
    hfrom M hMthreshold
  refine
    ⟨M, hM₀, by simpa only [hMsucc] using hqPrime, ?_⟩
  intro b hb hmean
  let : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hcoprime :
      Nat.Coprime (M + 1) (Nat.factorial (r + 1)) := by
    have hrankq : r + 1 < q := by
      simpa only [← hMsucc] using hrank
    have hqCoprime :
        Nat.Coprime q (Nat.factorial (r + 1)) :=
      hqPrime.coprime_factorial_of_lt hrankq
    simpa only [hMsucc] using hqCoprime
  exact
    relativeAPCount_lower_bound_of_linearFormsCondition
      happroximationError hcutError
      (wTrickedPrimeWeight_nonneg hα W b)
      (hmajorM b hb)
      (hν0 M b)
      hp
      (hLFM b hb)
      hcoprime
      hconvert
      (hweighted (M + 1))
      hmean
      (hcomparison M b hcoprime (hLFM b hb))
