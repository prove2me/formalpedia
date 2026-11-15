-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.16177+00:00
-- url     : https://prove2.me/submissions/83c1f363-871d-46b5-92c4-61b2e9e1b4b8

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_linearFormsProduct_eq_prod_selected
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_prod_normalizedSelbergMajorant_eq_divisorExpansion

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded divisor choices and congruence densities -/





















/-! ## One Selberg square -/







/-! ## A finite family of Selberg squares -/





/-! ## Normalized Selberg majorants -/







/-! ## CFZ specialization -/



theorem cfzWTrickedLinearValue_pos
    {k N : ℕ} [NeZero N]
    (W : ℕ) {b : ℕ} (hb : 0 < b)
    (q : CFZFormIndex k)
    (x : CubePoint k N) :
    0 < cfzWTrickedLinearValue W b q x := by
  unfold cfzWTrickedLinearValue wTrickedValue
  omega





end Wikipedia.SzemeredisTheorem

end

section


/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators















/-- The exact selected-family form of a cyclic-majorant subproduct. -/
theorem linearFormsProduct_cyclicMajorant_eq_prod_selected
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (e : LinearFormsExponent k)
    (x : CubePoint k N) :
    linearFormsProduct k N
        (χ.cyclicMajorant R W b) e x =
      ∏ q : SelectedCFZFormIndex e,
        χ.majorant R W
          (cfzWTrickedLinearValue W b q.1 x) := by
  rw [linearFormsProduct_eq_prod_selected]
  apply Fintype.prod_congr
  intro q
  rfl





end Wikipedia.SzemeredisTheorem

end
/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Exact paired-divisor expansion for every Boolean subproduct tested by
the cyclic linear-forms condition.  Unlike the full-family specialization
in `LinearFormsExpansion`, the indexing type here is the subtype selected by
the exponent `e`; no unselected Selberg factor is introduced. -/
theorem solution
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b)
    (e : LinearFormsExponent k) :
    mean
        (linearFormsProduct k N
          (χ.cyclicMajorant R W b) e) =
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∑ z ∈ smoothDivisorFamilyChoices
              (SelectedCFZFormIndex e) R,
            smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  cfzWTrickedLinearValue
                    (k := k) (N := N) W b q.1) z) := by
  classical
  rw [show
      linearFormsProduct k N
          (χ.cyclicMajorant R W b) e =
        fun x : CubePoint k N =>
          ∏ q : SelectedCFZFormIndex e,
            χ.majorant R W
              (cfzWTrickedLinearValue W b q.1 x) by
    funext x
    exact
      linearFormsProduct_cyclicMajorant_eq_prod_selected
        χ R W b e x]
  simpa only [SmoothSieveCutoff.majorant] using
    mean_prod_normalizedSelbergMajorant_eq_divisorExpansion
      χ.toFun χ.normalizer hR χ.zero_of_one_le
      (fun q : SelectedCFZFormIndex e =>
        cfzWTrickedLinearValue
          (k := k) (N := N) W b q.1)
      (fun q x => cfzWTrickedLinearValue_pos W hb q.1 x)
