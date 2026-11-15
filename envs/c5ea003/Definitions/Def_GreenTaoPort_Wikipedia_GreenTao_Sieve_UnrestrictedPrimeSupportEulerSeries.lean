-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:14:33.820684+00:00
-- url     : https://prove2.me/theorems/eabe6704-a238-42ad-8d3f-0339b6670034
-- title:
--   Terms in an unrestricted finite-prime-support expansion
-- statement:
--   For a complex prime-local factor $L(p)$ and a finite set $S$ of natural primes, the support term is
--
--   $$
--   \prod_{p\in S}(L(p)-1).
--   $$
--
--   The empty support contributes one. The specialized term uses the exact paired Fourier arithmetic local factor of a finite integer affine family, with the given sieve level and paired real frequency families. These definitions assign a term to each finite prime support; they impose neither a finite ambient prime cutoff nor a convergence assumption.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/UnrestrictedPrimeSupportEulerSeries.lean#L34-L679

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Lean
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Generic absolutely convergent support expansion -/

/-- The contribution of one finite set of active primes to an unrestricted
Euler expansion. -/
noncomputable def unrestrictedPrimeSupportTerm
    (localFactor : Nat.Primes → ℂ)
    (S : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ S, (localFactor p - 1)











/-! ## Absolute convergence of paired-Fourier local errors -/











/-! ## Direct-good-prime and carry-block versions -/





namespace SelectedCFZCarryFourierBlockData











end SelectedCFZCarryFourierBlockData

/-! ## Exact paired-Fourier specialization -/

/-- The unrestricted finite-prime-support term for the exact paired Fourier
local factors of an affine family. -/
noncomputable def unrestrictedPairedFourierPrimeSupportTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (S : Finset Nat.Primes) : ℂ :=
  unrestrictedPrimeSupportTerm
    (pairedFourierPrimeLocalFactor R forms t u) S



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.unrestrictedPrimeSupportTerm.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


