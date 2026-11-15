-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ReducedResidueCofinalTransference
-- name    : GreenTaoPort_Wikipedia_GreenTao_ReducedResidueCofinalTransference
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:18:19.629859+00:00
-- url     : https://prove2.me/theorems/9cf6eff2-ceec-4293-b0cc-715131f5fe9f
-- title:
--   Cofinal prime transference with reduced residue classes
-- statement:
--   Fix a progression length $k$, a prime-weight scale $\alpha$, a period $W$, and density and counting thresholds $\delta,c\in\mathbb R$. The cofinal transference predicate requires that, beyond every natural threshold $M_0$, there is $M\ge M_0$ with $M+1$ prime such that every reduced residue $b$ modulo $W$ satisfies
--
--   $$
--   \operatorname{mean}(f_b)\ge\delta\quad\Longrightarrow\quad
--   \operatorname{APCount}_k(f_b)\ge c,
--   $$
--
--   where $f_b$ is the $W$-tricked prime weight on $\mathbb Z/(M+1)\mathbb Z$. Thus the same selected prime modulus works for all reduced residues whose weight has the required mean. The standard-cutoff obligation asks, for every $k\ge3$, for a primorial period $W$ and a positive $c$ with this property, using the previously fixed prime scale and density target.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/ReducedResidueCofinalTransference.lean#L32-L172

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
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

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped Polynomial

/-- Cofinal-prime transference restricted to the reduced residue classes
that are actually produced by the W-trick density theorem. -/
def CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
    (k : ℕ) (α : ℝ) (W : ℕ) (δ c : ℝ) : Prop :=
  ∀ M₀ : ℕ,
    ∃ M : ℕ,
      M₀ ≤ M ∧ Nat.Prime (M + 1) ∧
        ∀ b : ℕ, b ∈ reducedResidues W →
          δ ≤
            mean
              (wTrickedPrimeWeight α W b :
                ZMod (M + 1) → ℝ) →
          c ≤
            cyclicAPCount k (M + 1)
              (wTrickedPrimeWeight α W b)



/-- The standard-cutoff cofinal obligation with reduced-residue membership
retained in the transference predicate. -/
def HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts :
    Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        k
        (primeScale k
          standardSmoothSieveCutoff.normalizer)
        (primorial w)
        (densityTarget k
          standardSmoothSieveCutoff.normalizer)
        c





end Wikipedia.SzemeredisTheorem


