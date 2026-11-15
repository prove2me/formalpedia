-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
-- name    : Wikipedia.SzemeredisTheorem.affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:39.897197+00:00
-- url     : https://prove2.me/theorems/3d5cc575-50a5-4e11-9259-6b2f40ca1c8f
-- title:
--   A rank-two affine family has common-zero density at most the inverse square
-- statement:
--   Let $p$ be prime and let integer affine forms have a finite coordinate type with decidable equality. If a finite selected support has affine rank at least two modulo $p$, then the density of its common zero set is at most $1/p^2$. No equality is asserted for the full selected family.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/GoodPrimeAffineRank.lean#L275-L298

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Rank-two affine densities at good primes

For a finite system of affine forms, failure of rank two modulo `p` is
detected by the vanishing of every two-by-two coefficient minor for some
distinct pair.  This file isolates a finite, explicit exceptional set using
the sum of the absolute values of all such minors.

Outside that set, pairwise independent integer coefficient vectors remain
rank two modulo `p`.  Thus every selected subfamily containing two distinct
indices has common-zero density at most `1 / p²`: its common-zero set is
contained in the common-zero set of one rank-two pair.  This is the actual
higher-order density estimate needed for the CFZ family.  Repeated indices do
not create rank, so the hypotheses use a `Finset` and explicitly require it
to be nontrivial.

The final results instantiate
`HasGoodPrimeHigherOrderDensityEstimate` for the CFZ forms and package the
estimate together with the exact local-factor inclusion--exclusion formula.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## An explicit finite exceptional set for rank two -/
/-! ## Selected-family rank and density -/

theorem Wikipedia.SzemeredisTheorem.affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
    {κ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (forms : κ → AffineForm ι ℤ)
    (s : Finset κ)
    (hrank :
      SelectedAffineFamilyHasRankAtLeastTwo p forms s) :
    affineFamilyZeroDensity p forms s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by sorry
