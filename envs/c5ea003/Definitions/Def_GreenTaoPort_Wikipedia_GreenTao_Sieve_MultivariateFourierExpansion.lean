-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:57:23.693272+00:00
-- url     : https://prove2.me/theorems/7174f9da-6832-4363-8353-429600bd3a69
-- title:
--   Fourier integrands for finite paired-divisor expansions
-- statement:
--   For a smooth cutoff $\chi$, natural level $R$, divisor family $(d_q)$, and real frequency family $(t_q)$, one transformed side is the product of the factors $\mu(d_q)F_\chi(t_q)$ times the logarithmic divisor phase at $(R,d_q,t_q)$. Here $F_\chi=\mathcal F(x\mapsto e^x\chi(x))$.
--
--   The paired coefficient multiplies the two sides corresponding to the two divisors and two frequency families. The complete finite Fourier integrand sums these transformed paired coefficients over the coordinatewise divisor choices, multiplying each by an arbitrary real arithmetic-density coefficient. The definitions separate the Fourier factors from that arithmetic input.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/MultivariateFourierExpansion.lean#L25-L147

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Mathlib.MeasureTheory.Integral.Prod
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
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-- One `κ`-variable half of the transformed paired-divisor coefficient. -/
noncomputable def transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) (t : κ → ℝ) : ℂ :=
  ∏ q,
    (ArithmeticFunction.moebius (d q) : ℂ) *
      χ.cutoffFourierTransform (t q) *
        divisorMultiplicativePhase R (d q) (t q)





/-- The full transformed coefficient for one paired divisor family. -/
noncomputable def transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  χ.transformedDivisorFamilySide R (fun q => (z q).1) tu.1 *
    χ.transformedDivisorFamilySide R (fun q => (z q).2) tu.2







/-- Fourier integrand for the entire finite divisor-family sum, with an
arbitrary real arithmetic coefficient attached to each family. -/
noncomputable def divisorExpansionFourierIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  ∑ z ∈ smoothDivisorFamilyChoices κ R,
    (density z : ℂ) *
      χ.transformedPairedDivisorFamily R z tu







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


