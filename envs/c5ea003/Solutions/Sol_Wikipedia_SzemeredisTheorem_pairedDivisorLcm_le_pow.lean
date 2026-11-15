-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedDivisorLcm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:26.509857+00:00
-- url     : https://prove2.me/submissions/ee8aa9f9-888f-4ad4-a597-f6d0613c823b

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

section







/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/

/-- The LCM of a finite family of natural numbers is at most their product.

The zero case is included: if one entry is zero, both the LCM and product are
zero. -/
theorem finset_lcm_le_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    s.lcm d ≤ ∏ i ∈ s, d i := by
  by_cases hprod : (∏ i ∈ s, d i) = 0
  · have hlcm : s.lcm d = 0 := by
      rw [Finset.lcm_eq_zero_iff, ← Finset.prod_eq_zero_iff]
      exact hprod
    simp [hlcm, hprod]
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hprod) (s.lcm_dvd_prod d)

/-- If every modulus in a finite family is at most `R`, their LCM is at most
`R` to the number of moduli. -/
theorem finset_lcm_le_pow_of_le {ι : Type*}
    (s : Finset ι) (d : ι → ℕ) (R : ℕ)
    (hd : ∀ i ∈ s, d i ≤ R) :
    s.lcm d ≤ R ^ s.card :=
  (finset_lcm_le_prod s d).trans
    (Finset.prod_le_pow_card s d R hd)





/-! ## Finite boxes -/

















/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/































end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Every term produced by `card κ` Selberg squares has period modulus at
most `R ^ (2 * card κ)`. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices κ R) :
    pairedDivisorLcm z ≤
      R ^ (2 * Fintype.card κ) := by
  have hzq :=
    Fintype.mem_piFinset.mp hz
  have hle :
      ∀ q : Sum κ κ,
        Sum.elim (fun i => (z i).1)
            (fun i => (z i).2) q ≤ R := by
    intro q
    cases q with
    | inl q =>
        exact
          (Finset.mem_Icc.mp
            (Finset.mem_product.mp (hzq q)).1).2
    | inr q =>
        exact
          (Finset.mem_Icc.mp
            (Finset.mem_product.mp (hzq q)).2).2
  unfold pairedDivisorLcm
  simpa [Fintype.card_sum, two_mul] using
    finset_lcm_le_pow_of_le
      (Finset.univ : Finset (Sum κ κ))
      (Sum.elim (fun i => (z i).1)
        (fun i => (z i).2))
      R (fun q _ => hle q)
