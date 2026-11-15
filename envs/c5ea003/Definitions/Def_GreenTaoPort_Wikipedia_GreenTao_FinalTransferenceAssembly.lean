-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_FinalTransferenceAssembly
-- name    : GreenTaoPort_Wikipedia_GreenTao_FinalTransferenceAssembly
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:21:39.983046+00:00
-- url     : https://prove2.me/theorems/24560c31-ddf1-4b75-b6ad-8eef8e35468b
-- title:
--   Removal and sieve interfaces for transference
-- statement:
--   Two predicates isolate the inputs used in the final transference argument. The removal predicate asks for uniform ordered pattern removal at parameters $(k,k-1)$ for every progression length $k\ge3$.
--
--   The sieve predicate fixes a requested error $\eta>0$ and then chooses a cutoff $w$ covering all exceptional primes of the concrete Conlon–Fox–Zhao affine system. Write $W=\prod_{p\le w}p$. At this fixed cutoff, for every sufficiently large cyclic modulus $M+1$, the standard smooth cyclic Selberg majorant at sieve level $R_k(M+1)$ must satisfy the linear-forms condition with error $\eta$, uniformly over all reduced residues $b\pmod W$.
--
--   The order of choices is part of the definition: the progression length and error are fixed before the primorial cutoff, and the modulus is chosen afterwards.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/FinalTransferenceAssembly.lean#L28-L52

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ReducedResidueCofinalTransference
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingParameterSelection
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Final dense/relative/sieve transference assembly

All elementary prime-density and extraction steps are already packaged by
`ReducedResidueCofinalTransference`.  This file performs the remaining
quantifier bookkeeping between the three deep inputs:

* ordered hypergraph removal, hence a positive uniform weighted dense AP
  count;
* the explicit relative-counting parameter package;
* the smooth cyclic-majorant linear-forms estimate.

The output is the corrected reduced-residue, cofinal-prime count predicate
consumed by the benchmark-facing theorem.  In particular the W-trick cutoff
is selected after the relative error, while the cyclic modulus is selected
only afterwards.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- Uniform ordered removal in precisely the ranks used to count arithmetic
progressions of every nontrivial length. -/
def HasOrderedRemovalForAllAPLengths : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    HasUniformOrderedPatternRemoval k (k - 1)

/-- The exact remaining smooth-sieve interface.

For every requested positive linear-forms error, one may choose a primorial
cutoff covering all fixed CFZ exceptional primes.  At that fixed cutoff the
standard cyclic Selberg majorant satisfies the linear-forms condition
eventually, uniformly over the reduced residue classes. -/
def HasStandardCyclicMajorantLinearForms : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ w : ℕ,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w ∧
          ∀ᶠ M : ℕ in atTop,
            ∀ b : ℕ, b ∈ reducedResidues (primorial w) →
              HasLinearFormsCondition k (M + 1)
                (standardSmoothSieveCutoff.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b)
                η





end Wikipedia.SzemeredisTheorem


