-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:29.542698+00:00
-- url     : https://prove2.me/submissions/d4946eb3-8d5f-4267-9084-b904ef99261c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AffineForm_mean_commonZeroFinsetZMod
import Theorems.Thm_Wikipedia_SzemeredisTheorem_affineFamilyCommonZeroFinset_subset_pair
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







@[simp]
theorem evalZMod_eq_zero_iff {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    ψ.evalZMod p x = 0 ↔
      ψ.linearMapZMod p x = -(ψ.constant : ZMod p) := by
  simp [evalZMod, eq_neg_iff_add_eq_zero, add_comm]



@[simp]
theorem mem_zeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ ψ.zeroFinsetZMod p ↔ ψ.evalZMod p x = 0 := by
  simp [zeroFinsetZMod, evalZMod_eq_zero_iff]











@[simp]
theorem mem_commonZeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ commonZeroFinsetZMod p ψ φ ↔
      ψ.evalZMod p x = 0 ∧ φ.evalZMod p x = 0 := by
  simp [commonZeroFinsetZMod]









/-- Multiplying the two zero-congruence indicators is exactly the indicator
of their simultaneous zero set. -/
theorem finsetIndicator_zero_mul_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x =
      finsetIndicator (commonZeroFinsetZMod p ψ φ) x := by
  simp only [finsetIndicator]
  by_cases hψ : ψ.evalZMod p x = 0 <;>
    by_cases hφ : φ.evalZMod p x = 0 <;>
    simp [hψ, hφ]

/-- Pairwise modular independence gives the exact second mixed moment of
the two congruence indicators. -/
theorem mean_zeroFinsetZMod_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    mean (fun x =>
      finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [show
    (fun x =>
      finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x) =
      finsetIndicator (commonZeroFinsetZMod p ψ φ) by
        funext x
        exact finsetIndicator_zero_mul_zero p ψ φ x]
  exact mean_commonZeroFinsetZMod hp ψ φ hdet

end AffineForm





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





/-- A two-element family is the existing mixed zero-indicator moment. -/
theorem affineFamilyZeroDensity_pair
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    {q r : κ} (hqr : q ≠ r) :
    affineFamilyZeroDensity p forms {q, r} =
      mean (fun x =>
        finsetIndicator ((forms q).zeroFinsetZMod p) x *
          finsetIndicator ((forms r).zeroFinsetZMod p) x) := by
  unfold affineFamilyZeroDensity
  congr 1
  funext x
  simp [affineFamilyZeroProduct, hqr]







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







/-- Common-zero density is monotone under adding selected forms. -/
theorem affineFamilyZeroDensity_le_pair
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) {q r : κ}
    (hq : q ∈ s) (hr : r ∈ s) :
    affineFamilyZeroDensity p forms s ≤
      affineFamilyZeroDensity p forms {q, r} := by
  rw [affineFamilyZeroDensity_eq_card,
    affineFamilyZeroDensity_eq_card]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast
    Finset.card_le_card
      (affineFamilyCommonZeroFinset_subset_pair
        p forms s hq hr)









/-! ## CFZ specialization -/



















end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## An explicit finite exceptional set for rank two -/
/-! ## Selected-family rank and density -/

open Wikipedia.SzemeredisTheorem in
/-- A selected rank-two witness gives the sharp upper bound `1 / p²` for
the full common-zero density.  Equality is used only for the witnessing
pair; additional forms may reduce the density. -/
theorem solution
    {κ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (forms : κ → AffineForm ι ℤ)
    (s : Finset κ)
    (hrank :
      SelectedAffineFamilyHasRankAtLeastTwo p forms s) :
    affineFamilyZeroDensity p forms s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  classical
  obtain ⟨q, hq, r, hr, hqr, i, j, hij⟩ := hrank
  calc
    affineFamilyZeroDensity p forms s ≤
        affineFamilyZeroDensity p forms {q, r} :=
      affineFamilyZeroDensity_le_pair
        p forms s hq hr
    _ = (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [affineFamilyZeroDensity_pair p forms hqr]
      exact AffineForm.mean_zeroFinsetZMod_mul
        hp (forms q) (forms r) hij
