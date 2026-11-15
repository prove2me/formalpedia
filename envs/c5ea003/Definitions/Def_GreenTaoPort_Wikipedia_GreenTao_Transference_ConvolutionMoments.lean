-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:52:35.119818+00:00
-- url     : https://prove2.me/theorems/468a6146-c94a-4276-8b45-a18efb4c41b1
-- title:
--   Expanded moments of generalized convolution tests
-- statement:
--   For a finite additive commutative group $G$, a real majorant $\nu$, and $n$ cut-test families on $(r+1)$-coordinate tuples, the expanded monomial moment averages $\nu(z)-1$ times the product of those cut tests over independent sum-fiber parameters. The normalized average runs over $z\in G$ and one $r$-coordinate fiber parameter for each test.
--
--   The general moment-bound predicate requires the absolute value of this moment to be at most $\eta$ for every $n\le d$ and every family of bounded cut tests. The Boolean version makes the same requirement only for the cut tests obtained from Boolean assignments. The parameters $r,d$ control the tuple dimension and maximum number of factors.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionMoments.lean#L18-L86

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The expanded fiber moment corresponding to a product of generalized
convolutions. -/
noncomputable def convolutionMonomialMoment
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (ν : G → ℝ) {n : ℕ}
    (u : Fin n → CutTestFamily G (r + 1)) : ℝ :=
  mean₂ fun z : G => fun y : Fin n → (Fin r → G) =>
    (ν z - 1) *
      ∏ a, cutTestProduct (u a)
        (sumFiberTuple r z (y a))





/-- Uniform expanded moment estimate for arbitrary bounded cut-test
families. -/
def HasConvolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r d : ℕ) (ν : G → ℝ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d →
    ∀ u : Fin n → CutTestFamily G (r + 1),
      (∀ a, IsBoundedCutTest (u a)) →
        |convolutionMonomialMoment r ν u| ≤ η

/-- The expanded moment estimate for the Boolean vertices needed by the
finite dense-model theorem. -/
def HasBooleanConvolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r d : ℕ) (ν : G → ℝ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d →
    ∀ b : Fin n → BooleanCutAssignment G (r + 1),
      |convolutionMonomialMoment r ν
        (fun a => cutTestFamilyOfBooleanAssignment (b a))| ≤ η









end Wikipedia.SzemeredisTheorem


