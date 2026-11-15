-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.complexWeightedLocalFactor_eq_firstOrder_add_remainder_of_goodPrime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:36.446179+00:00
-- url     : https://prove2.me/submissions/c24af5a0-5aee-46f2-8c08-b29357991e05

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_mean_zeroFinsetZMod
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedLocalFactor_eq_inclusionExclusion
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_powerset_supports_of_card_lt_two_complex

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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













@[simp]
theorem affineFamilyZeroDensity_empty
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    affineFamilyZeroDensity p forms ∅ = 1 := by
  unfold affineFamilyZeroDensity
  rw [show affineFamilyZeroProduct p forms ∅ =
      fun _x => (1 : ℝ) by
    funext x
    simp [affineFamilyZeroProduct]]
  exact mean_const (α := ι → ZMod p) 1

/-- A singleton family is the existing one-form zero density. -/
theorem affineFamilyZeroDensity_singleton
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (q : κ) :
    affineFamilyZeroDensity p forms {q} =
      mean (finsetIndicator ((forms q).zeroFinsetZMod p)) := by
  unfold affineFamilyZeroDensity
  congr 1
  funext x
  simp [affineFamilyZeroProduct]









/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















end Wikipedia.SzemeredisTheorem

end

section




/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/









/-! ## Scaling identities and W-trick preservation -/

















/-! ## Exact one- and two-form densities -/

/-- Direct modular one-form geometry gives exact singleton density without
an integer exceptional-bound hypothesis. -/
theorem affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms) (q : κ) :
    affineFamilyZeroDensity p forms {q} = (1 : ℝ) / p := by
  rw [affineFamilyZeroDensity_singleton]
  obtain ⟨i, hi⟩ := hgood.2 q
  exact AffineForm.mean_zeroFinsetZMod
    hgood.1 (forms q) hi







/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/

























end Wikipedia.SzemeredisTheorem

end
/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Modular one-form geometry -/
/-! ## Scaling identities and W-trick preservation -/
/-! ## Exact one- and two-form densities -/
/-! ## Complex first-order expansion from modular geometry -/

open Wikipedia.SzemeredisTheorem in
/-- Exact first-order expansion under the direct modular one-form
predicate.  This is the replacement for the integer-size-dependent
`complexWeightedLocalFactor_eq_firstOrder_add_remainder` at W-tricked
primes. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      1 - (∑ q, a q) / (p : ℂ) +
        complexWeightedLocalFactorRemainder p forms a := by
  let univSupports : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℂ :=
    fun s =>
      ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
        (affineFamilyZeroDensity p forms s : ℂ)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      univSupports (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ univSupports.filter (fun s => ¬2 ≤ s.card),
        term s) =
        1 - (∑ q, a q) / (p : ℂ) := by
    rw [show
        univSupports.filter (fun s => ¬2 ≤ s.card) =
          (Finset.univ : Finset κ).powerset.filter
            (fun s => ¬2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two_complex]
    simp only [term, Finset.card_empty, pow_zero,
      Finset.prod_empty, one_mul,
      affineFamilyZeroDensity_empty, Complex.ofReal_one,
      Finset.card_singleton, pow_one, Finset.prod_singleton]
    simp_rw [
      affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
        hnonzero]
    push_cast
    simp_rw [neg_one_mul, neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  rw [complexWeightedLocalFactor_eq_inclusionExclusion]
  change (∑ s ∈ univSupports, term s) =
    1 - (∑ q, a q) / (p : ℂ) +
      complexWeightedLocalFactorRemainder p forms a
  rw [← hsplit, hlow]
  unfold complexWeightedLocalFactorRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ univSupports.filter (fun s => 2 ≤ s.card), term s) +
        (1 - (∑ q, a q) / (p : ℂ)) =
      1 - (∑ q, a q) / (p : ℂ) +
        ∑ s ∈ univSupports.filter (fun s => 2 ≤ s.card), term s
  ac_rfl
