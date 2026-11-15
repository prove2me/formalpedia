-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_complexWeightedLocalFactorRemainder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:29.017573+00:00
-- url     : https://prove2.me/submissions/60b165cc-59a6-41cf-a947-d9bfac860cbe

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
import Theorems.Thm_Wikipedia_SzemeredisTheorem_affineFamilyZeroProduct_eq_indicator

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

























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











/-- Cardinality formula for an arbitrary finite-family common-zero density. -/
theorem affineFamilyZeroDensity_eq_card
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    affineFamilyZeroDensity p forms s =
      ((affineFamilyCommonZeroFinset p forms s).card : ℝ) /
        Fintype.card (ι → ZMod p) := by
  rw [affineFamilyZeroDensity,
    affineFamilyZeroProduct_eq_indicator]
  exact mean_finsetIndicator _













/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















end Wikipedia.SzemeredisTheorem

end

section


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



















/-! ## Selected-family rank and density -/



/-- A nontrivial selected finset has rank at least two at every rank-two
good prime. -/
theorem selectedAffineFamilyHasRankAtLeastTwo_of_goodPrime
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} (hgood : AffineRankTwoGoodPrime p forms)
    {s : Finset κ} (hs : s.Nontrivial) :
    SelectedAffineFamilyHasRankAtLeastTwo p forms s := by
  have hcard : 1 < s.card :=
    Finset.one_lt_card_iff_nontrivial.mpr hs
  obtain ⟨q, hq, r, hr, hqr⟩ :=
    Finset.one_lt_card.mp hcard
  exact ⟨q, hq, r, hr, hqr, hgood.2 hqr⟩





/-- Every affine-family zero density is nonnegative. -/
theorem affineFamilyZeroDensity_nonneg
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    0 ≤ affineFamilyZeroDensity p forms s := by
  rw [affineFamilyZeroDensity_eq_card]
  positivity



/-- Rank-two good primes give the same bound for every nontrivial selected
subfamily. -/
theorem affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p]
    {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (s : Finset κ) (hs : s.Nontrivial) :
    affineFamilyZeroDensity p forms s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  classical
  exact affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
    hgood.1 forms s
    (selectedAffineFamilyHasRankAtLeastTwo_of_goodPrime
      hgood hs)



/-! ## CFZ specialization -/



















end Wikipedia.SzemeredisTheorem

end

section


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



@[simp]
theorem mem_higherOrderSelectedSupports
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset κ) :
    s ∈ higherOrderSelectedSupports κ ↔ 2 ≤ s.card := by
  simp [higherOrderSelectedSupports]







/-! ## Quantitative remainder bounds -/



















/-! ## The existing unweighted local Euler factor -/







/-! ## CFZ specialization -/





end Wikipedia.SzemeredisTheorem

end
/-!
# Complex good-prime local factors after Fourier inversion

Fourier inversion turns each of the two smooth divisor sums attached to a
form into a complex multiplicative phase.  At a prime `p`, if the two phases
are `z` and `w`, the four squarefree divisor choices contribute

`1 - (z + w - z * w) 1_{p ∣ ψ(x)}`.

Thus the arithmetic local factor is a complex-weighted avoidance average.
This file develops that average directly over `ℂ`, proves its exact finite
inclusion--exclusion expansion, and isolates the singleton contribution.
At a rank-two good prime the remaining supports have density at most
`p⁻²`, so the complex remainder is bounded by the product of
`1 + ‖a q‖`.

For the Fourier coefficients, every divisor phase has norm at most one when
`R ≥ 2`, hence `‖z + w - z * w‖ ≤ 3`.  Consequently the higher-order
coefficient mass is at most `4 ^ m` for a system of `m` forms.  Above
`p ≥ 6m`, the complex first-order model has norm at least `1/2`; division by
that model therefore gives the explicit ratio estimate

`‖localRatio p - 1‖ ≤ 2 * 4 ^ m / p²`.

The final CFZ theorem masks the finite exceptional range and packages these
ratios in a complex analogue of `HasPrimeSquareError`, including
multipliability of the resulting remainder Euler product.

This does not yet compare the first-order model with the local factors of
the appropriate multivariate zeta quotient.  That analytic comparison, and
the subsequent parameter-uniform integration, are separate steps.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Complex finite averages -/
/-! ## Exact complex inclusion--exclusion -/
/-! ## Norm bounds for the complex remainder -/

open Wikipedia.SzemeredisTheorem in
/-- Rank two bounds the complex higher-order contribution by its total
coefficient norm mass times `p⁻²`. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactorRemainder p forms a‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  unfold complexWeightedLocalFactorRemainder
  calc
    ‖∑ s ∈ higherOrderSelectedSupports κ,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroDensity p forms s : ℂ)‖ ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          ‖((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ)‖ :=
      norm_sum_le
        (higherOrderSelectedSupports κ)
        (fun s =>
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ))
    _ ≤ ∑ s ∈ higherOrderSelectedSupports κ,
          (∏ q ∈ s, ‖a q‖) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs2 : 2 ≤ s.card :=
        (mem_higherOrderSelectedSupports s).mp hs
      have hsnontrivial : s.Nontrivial :=
        Finset.one_lt_card_iff_nontrivial.mp (by omega)
      have hdensity0 :
          0 ≤ affineFamilyZeroDensity p forms s :=
        affineFamilyZeroDensity_nonneg p forms s
      have hdensity :
          affineFamilyZeroDensity p forms s ≤
            (1 : ℝ) / (p : ℝ) ^ 2 :=
        affineFamilyZeroDensity_le_inv_sq_of_goodPrime
          hgood s hsnontrivial
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
        one_pow, one_mul, norm_prod, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hdensity0]
      exact mul_le_mul_of_nonneg_left hdensity
        (Finset.prod_nonneg fun q _hq => norm_nonneg (a q))
    _ = complexWeightedHigherOrderCoefficientMass a *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
      unfold complexWeightedHigherOrderCoefficientMass
      rw [Finset.sum_mul]
