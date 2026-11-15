-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_coordinatePrimePowerEquiv
-- name    : Wikipedia.SzemeredisTheorem.mean_coordinatePrimePowerEquiv
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:30.089857+00:00
-- url     : https://prove2.me/theorems/aa01f308-2422-4421-ae3b-056a82e3ec7d
-- title:
--   Multiplicativity of means under prime-power decomposition
-- statement:
--   Let $I$ be finite and let $D\ge1$ be an integer. For each prime $p\mid D$, let $e_p$ be its exponent in $D$ and let $F_p:(\mathbb Z/p^{e_p}\mathbb Z)^I\to\mathbb R$. The coordinatewise Chinese-remainder equivalence gives
--   $$
--   \mathbb E_{x\in(\mathbb Z/D\mathbb Z)^I}\prod_{p\mid D}F_p(x\bmod p^{e_p})
--   =\prod_{p\mid D}\mathbb E_{y\in(\mathbb Z/p^{e_p}\mathbb Z)^I}F_p(y).
--   $$
--   The products run over distinct prime factors, and the normalized-mean identity includes $D=1$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PairedDivisibilityCRT.lean#L405-L430

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
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
# CRT factorization of paired divisibility densities

The divisor expansion of a product of Selberg weights leaves an exact finite
density `pairedDivisibilityDensity`.  This file isolates the arithmetic steps
which can be performed without any analytic estimate.

First, the two divisor conditions attached to one form are replaced by their
least common multiple.  The resulting zero--one function is identified with
the indicator of its exact finite support, and each nonzero local modulus is
then decomposed into its prime-power divisibility conditions.

Second, normalized means are reindexed by the Chinese remainder theorem.
For any finite pairwise-coprime family of moduli, a product of functions which
depends separately on the corresponding CRT components has mean equal to the
product of its local means.  We specialize this both to two moduli and to the
canonical prime-power decomposition of a nonzero modulus.

For arbitrary natural-valued forms, CRT factorization is not automatic: one
must still show that the global paired divisibility indicator depends on the
CRT components as a product of local indicators.  The final definitions and
theorems package precisely that remaining obligation, without asserting a
false independence statement.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Collapsing paired divisibility conditions -/
/-! ## Prime-power divisibility data -/
/-! ## Exact factorization of finite means by CRT -/
/-! ## Canonical prime-power CRT -/

theorem Wikipedia.SzemeredisTheorem.mean_coordinatePrimePowerEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} [NeZero D]
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ) :
    mean (fun x : ι → ZMod D =>
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) =
      ∏ p, mean (localFactor p) := by sorry
