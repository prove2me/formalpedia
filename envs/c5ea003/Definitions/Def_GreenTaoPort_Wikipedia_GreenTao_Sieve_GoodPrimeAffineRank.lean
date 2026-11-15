-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:47.973964+00:00
-- url     : https://prove2.me/theorems/6ae07c62-3274-4a57-b2d2-ed9c4be852ae
-- title:
--   Rank-two conditions for affine coefficient families modulo a prime
-- statement:
--   For a finite family of integer affine forms $(\psi_q)$, a rank-two good prime is a natural prime $p$ such that every two distinct form indices $q,r$ admit variable indices $i,j$ with
--
--   $$
--   \psi_{q,i}\psi_{r,j}-\psi_{q,j}\psi_{r,i}\ne0
--   \quad\text{in }\mathbb Z/p\mathbb Z.
--   $$
--
--   The selected-family predicate requires the existence of one such distinct pair inside a specified finite subset of form indices. This second predicate does not itself require $p$ to be prime. Both conditions concern coefficient vectors; affine constant terms do not enter the minors, and repeating an index cannot supply the required rank.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/GoodPrimeAffineRank.lean#L134-L209

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## An explicit finite exceptional set for rank two -/











/-- Every two distinct forms have a nonzero two-by-two minor modulo a
rank-two good prime. -/
def AffineRankTwoGoodPrime
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ) : Prop :=
  p.Prime ∧
    ∀ {q r : κ}, q ≠ r →
      ∃ i j : ι,
        (((forms q).coefficientMinor (forms r) i j : ℤ) :
          ZMod p) ≠ 0







/-! ## Selected-family rank and density -/

/-- A selected family has rank at least two modulo `p` when it contains two
distinct indices with a nonvanishing coefficient minor.  Repetition alone
cannot witness this predicate. -/
def SelectedAffineFamilyHasRankAtLeastTwo
    {κ ι : Type*} [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : Prop :=
  ∃ q ∈ s, ∃ r ∈ s, q ≠ r ∧
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0















/-! ## CFZ specialization -/



















end Wikipedia.SzemeredisTheorem


