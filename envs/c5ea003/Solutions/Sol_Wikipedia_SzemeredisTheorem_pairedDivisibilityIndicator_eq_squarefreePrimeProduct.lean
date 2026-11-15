-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedDivisibilityIndicator_eq_squarefreePrimeProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.577134+00:00
-- url     : https://prove2.me/submissions/fd550ef4-f20c-4c6c-be31-9eeaec756b7c

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_dvd_iff_primePower_dvd
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mem_primeFactors_pairedDivisorLcm_iff

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





/-- Two divisibility indicators at the same value collapse to the indicator
of the least common multiple.  The statement includes zero moduli. -/
theorem natDivisibilityIndicator_mul_eq_lcm
    (a b n : ℕ) :
    natDivisibilityIndicator a n *
        natDivisibilityIndicator b n =
      natDivisibilityIndicator (Nat.lcm a b) n := by
  simp only [natDivisibilityIndicator, Nat.lcm_dvd_iff]
  by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;>
    simp [ha, hb]

/-- The paired indicator is the product of the indicators for the local
least common multiples. -/
theorem pairedDivisibilityIndicator_eq_lcmProduct
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ) (x : X) :
    pairedDivisibilityIndicator values z x =
      ∏ q, natDivisibilityIndicator
        (pairedLocalModulus z q) (values q x) := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  exact natDivisibilityIndicator_mul_eq_lcm
    (z q).1 (z q).2 (values q x)











/-! ## Prime-power divisibility data -/









/-! ## Exact factorization of finite means by CRT -/



















/-! ## Canonical prime-power CRT -/





/-! ## Conditional factorization interfaces for paired densities -/









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



@[simp]
theorem mem_pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) (q : κ) :
    q ∈ pairedPrimeSupport z p ↔ p ∣ pairedLocalModulus z q := by
  simp [pairedPrimeSupport]







/-! ## Arbitrary finite-family intersection densities -/

























/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















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

open Wikipedia.SzemeredisTheorem in
/-- For squarefree choices, the paired indicator is exactly a product over
the primes of the global LCM, with one factor for every form containing that
prime. -/
theorem solution
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z) (x : X) :
    pairedDivisibilityIndicator values z x =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        squarefreePairedPrimeIndicator values z p x := by
  classical
  by_cases hx :
      ∀ q, pairedLocalModulus z q ∣ values q x
  · have hleft :
        pairedDivisibilityIndicator values z x = 1 := by
      rw [pairedDivisibilityIndicator_eq_lcmProduct]
      apply Finset.prod_eq_one
      intro q _hq
      simp [natDivisibilityIndicator, hx q]
    have hright :
        (∏ p : (pairedDivisorLcm z).primeFactors,
          squarefreePairedPrimeIndicator values z p x) = 1 := by
      apply Finset.prod_eq_one
      intro p _hp
      unfold squarefreePairedPrimeIndicator
      apply Finset.prod_eq_one
      intro q hq
      have hpq :
          (p : ℕ) ∣ pairedLocalModulus z q :=
        (mem_pairedPrimeSupport z p q).mp hq
      simp [natDivisibilityIndicator, hpq.trans (hx q)]
    rw [hleft, hright]
  · simp only [not_forall] at hx
    obtain ⟨q, hq⟩ := hx
    have hm0 : pairedLocalModulus z q ≠ 0 :=
      (squarefree_pairedLocalModulus hz q).ne_zero
    have hprimePower :
        ¬ ∀ p : (pairedLocalModulus z q).primeFactors,
          (p : ℕ) ^
              (pairedLocalModulus z q).factorization p ∣
            values q x := by
      exact fun h => hq ((dvd_iff_primePower_dvd hm0).mpr h)
    simp only [not_forall] at hprimePower
    obtain ⟨p, hpvalue⟩ := hprimePower
    have hpexponent :
        (pairedLocalModulus z q).factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree
        (squarefree_pairedLocalModulus hz q)
        (Nat.prime_of_mem_primeFactors p.2)
        (Nat.dvd_of_mem_primeFactors p.2)
    have hpnot : ¬ (p : ℕ) ∣ values q x := by
      simpa [hpexponent] using hpvalue
    have hpD :
        (p : ℕ) ∈ (pairedDivisorLcm z).primeFactors := by
      rw [mem_primeFactors_pairedDivisorLcm_iff hz]
      exact
        ⟨Nat.prime_of_mem_primeFactors p.2,
          ⟨q, by
            exact (mem_pairedPrimeSupport z p q).mpr
              (Nat.dvd_of_mem_primeFactors p.2)⟩⟩
    let pD : (pairedDivisorLcm z).primeFactors :=
      ⟨p, hpD⟩
    have hleft :
        pairedDivisibilityIndicator values z x = 0 := by
      rw [pairedDivisibilityIndicator_eq_lcmProduct]
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      simp [natDivisibilityIndicator, hq]
    have hright :
        (∏ r : (pairedDivisorLcm z).primeFactors,
          squarefreePairedPrimeIndicator values z r x) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ pD)
      unfold squarefreePairedPrimeIndicator
      apply Finset.prod_eq_zero
      · exact (mem_pairedPrimeSupport z pD q).mpr
          (Nat.dvd_of_mem_primeFactors p.2)
      · simp [natDivisibilityIndicator, pD, hpnot]
    rw [hleft, hright]
