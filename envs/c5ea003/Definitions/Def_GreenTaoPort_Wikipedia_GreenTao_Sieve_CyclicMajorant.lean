-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:58:24.156689+00:00
-- url     : https://prove2.me/theorems/2da4425b-275f-445c-badd-4b0567a81409
-- title:
--   Global cyclic Selberg majorants and selected form indices
-- statement:
--   For a smooth sieve cutoff $\chi$, natural parameters $R,W,b$, and a positive cyclic modulus $N$, the global cyclic majorant evaluates the normalized Selberg weight at the standard representative of the affine residue:
--
--   $$
--   \nu(n)=\chi.\operatorname{majorant}(R,W,W\widetilde n+b),
--   \qquad n\in\mathbb Z/N\mathbb Z.
--   $$
--
--   Here $\widetilde n\in\{0,\ldots,N-1\}$ is the natural representative. The weight is defined on the whole cyclic group, without restricting it to the short interval used for the prime weight. The bundle also supplies the finite subtype of CFZ forms selected by a Boolean linear-forms exponent: an indexed form belongs precisely when its Boolean selection value is true.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CyclicMajorant.lean#L24-L76

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The smooth Selberg majorant evaluated on the standard representative of
a W-tricked cyclic residue, without interval localization. -/
noncomputable def SmoothSieveCutoff.cyclicMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (n : ZMod N) : ℝ :=
  χ.majorant R W (wTrickedValue W b n)







/-- The finite type of CFZ forms selected by a Boolean linear-forms
exponent. -/
abbrev SelectedCFZFormIndex {k : ℕ}
    (e : LinearFormsExponent k) :=
  {q : CFZFormIndex k // e q.1 q.2 = true}











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cyclicMajorant.congr_simp,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cyclicMajorant.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


