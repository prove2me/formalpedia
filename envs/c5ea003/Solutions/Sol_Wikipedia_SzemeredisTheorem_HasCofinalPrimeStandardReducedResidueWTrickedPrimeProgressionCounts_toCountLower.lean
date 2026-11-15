-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts.toCountLower
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:56:04.629437+00:00
-- url     : https://prove2.me/submissions/0bfbc1f0-a42f-454d-aa50-992d34c7a273

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_densityTarget_le_primeScale_mul_log_div
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_forall_pos_exists_reducedResidue_mean_ge

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)



theorem primeScale_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < primeScale k cutoffNormalizer := by
  rw [primeScale]
  exact lt_min (by norm_num)
    (div_pos (sieveExponent_pos hk)
      (mul_pos (by norm_num) hnorm))

























end Wikipedia.SzemeredisTheorem

end

section





namespace Wikipedia.SzemeredisTheorem

open Finset



@[simp]
theorem mem_reducedResidues {W b : ℕ} :
    b ∈ reducedResidues W ↔ b < W ∧ W.Coprime b := by
  simp [reducedResidues]























end Wikipedia.SzemeredisTheorem

end

section







/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff



namespace SmoothSieveCutoff





















end SmoothSieveCutoff







theorem standardSmoothSieveCutoff_normalizer_pos :
    0 < standardSmoothSieveCutoff.normalizer :=
  standardSmoothSieveCutoff.normalizer_pos



end Wikipedia.SzemeredisTheorem

end

section






/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/

namespace Wikipedia.SzemeredisTheorem

open Finset Real Filter
open scoped BigOperators



































































/-- Threshold form of the uniform W-tricked density statement, ready for
the nested choices in the final assembly. -/
theorem exists_threshold_reducedResidue_mean_ge
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∃ b ∈ reducedResidues (primorial w),
        α * log 2 / 128 ≤
          mean
            (wTrickedPrimeWeight α (primorial w) b :
              ZMod N → ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1
      (eventually_forall_pos_exists_reducedResidue_mean_ge hα)
  refine ⟨N₀, ?_⟩
  intro N hN hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  exact hN₀ N hN hNpos

/-- The uniform density theorem specialized to the globally fixed
Green--Tao parameter choices.  In particular, this statement fixes the
density before choosing the residue class and cyclic modulus. -/
theorem exists_threshold_reducedResidue_mean_ge_densityTarget
    {k w : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∃ b ∈ reducedResidues (primorial w),
        densityTarget k cutoffNormalizer ≤
          mean
            (wTrickedPrimeWeight
              (primeScale k cutoffNormalizer)
              (primorial w) b : ZMod N → ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_threshold_reducedResidue_mean_ge
      (primeScale_pos hk hnorm) (w := w)
  refine ⟨N₀, ?_⟩
  intro N hN hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  obtain ⟨b, hb, hmean⟩ := hN₀ N hN hNpos
  exact ⟨b, hb,
    (densityTarget_le_primeScale_mul_log_div hk hnorm).trans
      hmean⟩



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

/-- Corrected cofinal transference combines directly with the existing
reduced-residue density theorem.  Only the final elementary count-lower
interface forgets coprimality, since prime extraction no longer needs it. -/
theorem
    solution
    (htransfer :
      HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts) :
    HasCofinalPrimeWTrickedPrimeProgressionCountLower := by
  intro k hk
  obtain ⟨w, c, hc, htransferCofinal⟩ :=
    htransfer k hk
  refine
    ⟨primeScale k standardSmoothSieveCutoff.normalizer,
      primorial w, c,
      primeScale_pos hk
        standardSmoothSieveCutoff_normalizer_pos,
      primorial_pos w, hc, ?_⟩
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_threshold_reducedResidue_mean_ge_densityTarget
      (w := w) hk
        standardSmoothSieveCutoff_normalizer_pos
  intro M₀
  obtain ⟨M, hMlarge, hprime, htransferM⟩ :=
    htransferCofinal (max M₀ Ndensity)
  have hM₀ : M₀ ≤ M :=
    (le_max_left M₀ Ndensity).trans hMlarge
  have hNdensity : Ndensity ≤ M + 1 :=
    (le_max_right M₀ Ndensity).trans
      (hMlarge.trans (Nat.le_succ M))
  obtain ⟨b, hb, hmean⟩ :=
    hdensity (M + 1) hNdensity (Nat.succ_pos M)
  exact
    ⟨M, hM₀, hprime, b,
      (mem_reducedResidues.mp hb).1,
      htransferM b hb hmean⟩
