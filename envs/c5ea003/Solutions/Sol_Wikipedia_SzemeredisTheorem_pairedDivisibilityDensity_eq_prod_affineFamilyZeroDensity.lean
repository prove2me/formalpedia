-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.063036+00:00
-- url     : https://prove2.me/submissions/1ef11909-064f-459b-8ccb-8972138bd959

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_coordinatePrimePowerEquiv
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityIndicator_eq_affinePrimeProduct

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



















/-! ## Canonical prime-power CRT -/





/-! ## Conditional factorization interfaces for paired densities -/







/-- Canonical prime-power factorization of a paired divisibility density,
conditional only on the explicit pointwise local-separation statement. -/
theorem pairedDivisibilityDensity_eq_prod_primePowerMeans
    {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {D : ℕ} [NeZero D]
    (values : κ → (ι → ZMod D) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ)
    (hfactor :
      PairedDivisibilityFactorsOverPrimePowers
        values z localFactor) :
    pairedDivisibilityDensity values z =
      ∏ p, mean (localFactor p) := by
  calc
    pairedDivisibilityDensity values z =
        mean (fun x : ι → ZMod D =>
          ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) := by
      unfold pairedDivisibilityDensity
      congr 1
      funext x
      exact hfactor x
    _ = ∏ p, mean (localFactor p) :=
      mean_coordinatePrimePowerEquiv localFactor

end Wikipedia.SzemeredisTheorem

end

section






/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Squarefree divisor choices -/

















/-! ## Exact prime support and the squarefree indicator product -/











/-! ## Arbitrary finite-family intersection densities -/

























/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/







/-- The mean of the transported canonical prime-power factor is exactly the
finite-family density over the forms containing that prime. -/
theorem mean_affinePairedPrimeFactor_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    mean (affinePairedPrimeFactor forms z hz p) =
      affineFamilyZeroDensity (p : ℕ) forms
        (pairedPrimeSupport z p) := by
  unfold affinePairedPrimeFactor affineFamilyZeroDensity mean
  apply Fintype.expect_equiv
    (squarefreePrimePowerEquiv hz p)
  intro x
  rfl











end Wikipedia.SzemeredisTheorem

end
/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Squarefree divisor choices -/
/-! ## Exact prime support and the squarefree indicator product -/
/-! ## Arbitrary finite-family intersection densities -/
/-! ## Exact arbitrary-family local factor formula -/
/-! ## Localization of the canonical CRT factors -/

open Wikipedia.SzemeredisTheorem in
/-- Squarefree paired divisor densities localize exactly to the arbitrary
finite-family affine densities, one for the forms containing each prime. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz) :
    pairedDivisibilityDensity values z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) := by
  calc
    pairedDivisibilityDensity values z =
        ∏ p : (pairedDivisorLcm z).primeFactors,
          mean (affinePairedPrimeFactor forms z hz p) := by
      apply pairedDivisibilityDensity_eq_prod_primePowerMeans
        values z (affinePairedPrimeFactor forms z hz)
      intro x
      exact pairedDivisibilityIndicator_eq_affinePrimeProduct
        z values forms hz hmodel x
    _ = ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact mean_affinePairedPrimeFactor_eq forms z hz p
