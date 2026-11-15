-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisorLcm_le_pow
-- name    : Wikipedia.SzemeredisTheorem.pairedDivisorLcm_le_pow
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:13.864435+00:00
-- url     : https://prove2.me/theorems/6a59557c-51c2-4c18-a2ab-039771763960
-- title:
--   A supported divisor family has bounded LCM
-- statement:
--   Let $\kappa$ be finite with decidable equality and let a paired-divisor family $z$ belong to the smooth divisor-family choices at natural scale $R$. Then its global paired-divisor LCM is at most $R^{2|\kappa|}$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LinearFormsExpansion.lean#L113-L143

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
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
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
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
# Exact finite expansion of Selberg weights along linear forms

This file performs the algebraic expansion that precedes the analytic
Goldston--Yıldırım estimate.  For a finite family of positive
natural-valued forms, the mean of a product of smooth Selberg squares is
written exactly as a finite sum over two bounded divisor choices per form.
Each term splits into

* a product of smooth Möbius-cutoff coefficients; and
* the exact density of the simultaneous divisibility congruences.

The least common multiple of the chosen divisors is bounded by
`R ^ (2 * card κ)`, using `CongruenceAverage`.  The final section
specializes the identity to the full CFZ family evaluated through
`apLinearForm` and the natural W-tricked lift.

There are no asymptotic estimates here.  Factoring the composite-modulus
congruence density into prime local factors, controlling the exceptional
primes, and bounding the resulting Euler product remain separate analytic
steps.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Bounded divisor choices and congruence densities -/

theorem Wikipedia.SzemeredisTheorem.pairedDivisorLcm_le_pow
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices κ R) :
    pairedDivisorLcm z ≤
      R ^ (2 * Fintype.card κ) := by sorry
