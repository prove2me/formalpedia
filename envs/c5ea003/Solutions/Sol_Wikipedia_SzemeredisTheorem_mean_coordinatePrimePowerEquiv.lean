-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_coordinatePrimePowerEquiv
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:54:40.97768+00:00
-- url     : https://prove2.me/submissions/813ea59c-a712-47e7-92b5-69c347391d7b

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

section




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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Collapsing paired divisibility conditions -/



















/-! ## Prime-power divisibility data -/









/-! ## Exact factorization of finite means by CRT -/



/-- A dependent version of `prod_mean`: a product of normalized means is the
mean over an independent choice from each (possibly different) finite type. -/
theorem prod_mean_pi
    {τ : Type*} [Fintype τ] [DecidableEq τ]
    {β : τ → Type*}
    [∀ t, Fintype (β t)] [∀ t, Nonempty (β t)]
    (F : ∀ t, β t → ℝ) :
    (∏ t, mean (F t)) =
      mean (fun y : ∀ t, β t => ∏ t, F t (y t)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp















/-! ## Canonical prime-power CRT -/





/-! ## Conditional factorization interfaces for paired densities -/









end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- A product of prime-power-local functions has exactly multiplicative mean
when pulled back to residue vectors modulo the composite modulus. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} [NeZero D]
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ) :
    mean (fun x : ι → ZMod D =>
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) =
      ∏ p, mean (localFactor p) := by
  classical
  calc
    mean (fun x : ι → ZMod D =>
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) =
        mean (fun y :
          ∀ p : D.primeFactors,
            ι → ZMod ((p : ℕ) ^ D.factorization p) =>
          ∏ p, localFactor p (y p)) := by
      unfold mean
      apply Fintype.expect_equiv
        coordinatePrimePowerEquiv
      intro x
      rfl
    _ = ∏ p, mean (localFactor p) :=
      (prod_mean_pi localFactor).symm
