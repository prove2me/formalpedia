-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:01:39.029186+00:00
-- url     : https://prove2.me/theorems/db9013b1-cf33-49ac-99bb-d3eefc5d2bf3
-- title:
--   Higher-order supports in finite local-factor expansions
-- statement:
--   For a finite type $K$ of form indices, the higher-order support set is
--
--   $$
--   \{S\subseteq K:|S|\ge2\}.
--   $$
--
--   It is represented as the power set of the full finite index set, filtered by the cardinality condition. This separates the terms beyond the empty and singleton supports in finite inclusion–exclusion expansions of local factors. The definition depends only on the finite index type and its decidable equality; prime moduli, coefficient weights, and affine forms enter the later estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/GoodPrimeLocalFactorBound.lean#L99-L104

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Lean
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
# Quantitative good-prime local-factor remainder

This file turns the rank-two common-zero estimate into the finite
inclusion--exclusion bound used by the local Euler-factor calculation.

We allow an arbitrary real coefficient `a q` on the zero indicator of each
form.  The empty support contributes exactly `1`, the singleton supports
contribute exactly `-(∑ q, a q) / p`, and every support of cardinality at
least two has density at most `1 / p²` at a rank-two good prime.  Hence the
remaining contribution is bounded by

`(∑ S, 2 ≤ S.card, ∏ q ∈ S, |a q|) / p²`.

This finite coefficient mass is also bounded by `∏ q, (1 + |a q|)`.  Taking
all coefficients equal to one recovers the unweighted avoidance product from
`LocalEulerFactors` and gives an explicit `2 ^ card κ / p²` error.  No
infinite Euler product or convergence statement is made here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Weighted finite inclusion--exclusion -/







/-! ## Separating empty and singleton supports -/

/-- Supports of cardinality at least two in the full finite family. -/
def higherOrderSelectedSupports
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Finset (Finset κ) :=
  (Finset.univ : Finset κ).powerset.filter
    fun s => 2 ≤ s.card









/-! ## Quantitative remainder bounds -/



















/-! ## The existing unweighted local Euler factor -/







/-! ## CFZ specialization -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.higherOrderSelectedSupports.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


