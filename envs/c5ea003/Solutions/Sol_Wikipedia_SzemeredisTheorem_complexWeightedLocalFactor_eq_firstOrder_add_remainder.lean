-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.complexWeightedLocalFactor_eq_firstOrder_add_remainder
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:36.441146+00:00
-- url     : https://prove2.me/submissions/c980ed51-17c9-4744-9cd5-eae5a5c19cb5

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_mean_zeroFinsetZMod
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedLocalFactor_eq_inclusionExclusion
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_powerset_supports_of_card_lt_two_complex

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm



end AffineForm

theorem intCast_zmod_ne_zero_of_natAbs_lt
    {p : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hzp : Int.natAbs z < p) :
    (z : ZMod p) ≠ 0 := by
  intro hzero
  have hpdivInt : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzero
  have hpdiv : p ∣ Int.natAbs z := by
    simpa using
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := z)).2 hpdivInt
  have hzpos : 0 < Int.natAbs z :=
    (Int.natAbs_pos.mpr hz)
  have hple : p ≤ Int.natAbs z :=
    Nat.le_of_dvd hzpos hpdiv
  omega



theorem coefficient_natAbs_le_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) (q : κ) (i : ι) :
    Int.natAbs ((forms q).coefficient i) ≤
      exceptionalPrimeBound forms := by
  have hi :
      Int.natAbs ((forms q).coefficient i) ≤
        ∑ j : ι, Int.natAbs ((forms q).coefficient j) :=
    Finset.single_le_sum
      (f := fun j : ι =>
        Int.natAbs ((forms q).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hq :
      (∑ j : ι, Int.natAbs ((forms q).coefficient j)) ≤
        ∑ r : κ, ∑ j : ι,
          Int.natAbs ((forms r).coefficient j) :=
    Finset.single_le_sum
      (f := fun r : κ =>
        ∑ j : ι, Int.natAbs ((forms r).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact (hi.trans hq).trans (Nat.le_add_right _ _)





/-- Beyond the explicit bound, every nonzero coefficient vector retains a
nonzero coefficient modulo `p`. -/
theorem exists_coefficient_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    (q : κ) :
    ∃ i : ι, ((forms q).coefficient i : ZMod p) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hforms q)
  refine ⟨i, intCast_zmod_ne_zero_of_natAbs_lt hi ?_⟩
  exact (coefficient_natAbs_le_exceptionalPrimeBound forms q i).trans_lt hp



end Wikipedia.SzemeredisTheorem

end

section





/-!
# Elementary local densities of affine forms

This starts the local-factor calculation with the exact one-form density.
An integer affine form is reduced modulo `p`; if one coefficient remains
nonzero and `p` is prime, its linear part is surjective.  All fibers then
have the same cardinality, so the zero congruence occupies exactly a
`1 / p` fraction of the finite vector space (recorded first as an exact
natural-number identity).
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





































end AffineForm

/-- Beyond the explicit exceptional-prime bound, every form in a nonzero
system has exact zero-congruence density `1 / p`. -/
theorem mean_zeroFinsetZMod_of_bound
    {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (q : κ) :
    mean (finsetIndicator ((forms q).zeroFinsetZMod p)) =
      (1 : ℝ) / p := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_coefficient_cast_ne_zero_of_bound hforms hlarge q
  exact AffineForm.mean_zeroFinsetZMod hp (forms q) hi



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



/-- Exact singleton density outside the exceptional-prime range. -/
theorem affineFamilyZeroDensity_singleton_of_bound
    {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) (q : κ) :
    affineFamilyZeroDensity p forms {q} = (1 : ℝ) / p := by
  classical
  rw [affineFamilyZeroDensity_singleton]
  exact mean_zeroFinsetZMod_of_bound hforms hp hlarge q





/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















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

open Wikipedia.SzemeredisTheorem in
/-- Exact first-order decomposition of the complex local factor. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      1 - (∑ q, a q) / (p : ℂ) +
        complexWeightedLocalFactorRemainder p forms a := by
  let u : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℂ :=
    fun s =>
      ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
        (affineFamilyZeroDensity p forms s : ℂ)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      u (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ u.filter (fun s => ¬ 2 ≤ s.card),
        term s) =
        1 - (∑ q, a q) / (p : ℂ) := by
    rw [show u.filter (fun s => ¬ 2 ≤ s.card) =
        (Finset.univ : Finset κ).powerset.filter
          (fun s => ¬ 2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two_complex]
    simp only [term, Finset.card_empty, pow_zero,
      Finset.prod_empty, one_mul,
      affineFamilyZeroDensity_empty, Complex.ofReal_one,
      Finset.card_singleton, pow_one, Finset.prod_singleton]
    simp_rw [affineFamilyZeroDensity_singleton_of_bound
      hnonzero hp hlarge]
    push_cast
    simp_rw [neg_one_mul, neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  rw [complexWeightedLocalFactor_eq_inclusionExclusion]
  change (∑ s ∈ u, term s) =
    1 - (∑ q, a q) / (p : ℂ) +
      complexWeightedLocalFactorRemainder p forms a
  rw [← hsplit, hlow]
  unfold complexWeightedLocalFactorRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s) +
        (1 - (∑ q, a q) / (p : ℂ)) =
      1 - (∑ q, a q) / (p : ℂ) +
        ∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s
  ac_rfl
