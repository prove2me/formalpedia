-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HasComplexPrimeSquareError_tendsto_tprod_one
-- name    : Wikipedia.SzemeredisTheorem.HasComplexPrimeSquareError.tendsto_tprod_one
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:43.581331+00:00
-- url     : https://prove2.me/theorems/65a3f72a-7ef0-4cf2-a25c-2c835ad1370c
-- title:
--   Dominated convergence for prime-indexed Euler products
-- statement:
--   Let $\mathcal F$ be a filter on a type $A$, and let $a_{n,p}\in\mathbb C$ be indexed by $n\in A$ and primes $p$. Suppose a common constant $C$ gives the prime-square error bound eventually along $\mathcal F$, and $a_{n,p}\to1$ along $\mathcal F$ for each prime $p$. Then the unordered Euler products $\prod_p a_{n,p}$ tend to $1$ along $\mathcal F$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ComplexEulerProductTail.lean#L30-L70

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Uniform tails of complex Euler products

The local estimates used in the smooth sieve are uniform in the Fourier
variables but the local-factor family itself changes with all asymptotic
parameters.  Ordinary convergence of one fixed Euler product is therefore
not enough.

This file packages the required dominated-convergence statement.  If a
varying family has the common bound

`‖L_n(p) - 1‖ ≤ C / p²`

and each fixed prime factor tends to one, then the full unordered products
also tend to one.  A second theorem specializes this to the standard
large-prime mask: all factors at `p ≤ w_n` are replaced by one, and
`w_n → ∞`.  No bound on the Fourier variables is needed because the local
square-error estimate is already uniform in them.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology

theorem Wikipedia.SzemeredisTheorem.HasComplexPrimeSquareError.tendsto_tprod_one
    {α : Type*} {𝓕 : Filter α}
    {C : ℝ} {localFactor : α → Nat.Primes → ℂ}
    (herror :
      ∀ᶠ n in 𝓕,
        HasComplexPrimeSquareError C (localFactor n))
    (hpoint :
      ∀ p : Nat.Primes,
        Tendsto (fun n => localFactor n p)
          𝓕 (𝓝 1)) :
    Tendsto
      (fun n => ∏' p : Nat.Primes, localFactor n p)
      𝓕 (𝓝 1) := by sorry
