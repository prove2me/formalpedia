-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.affineFamilyZeroProduct_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:44:20.402918+00:00
-- url     : https://prove2.me/submissions/6ecefef0-20f0-47d0-9f18-548439013cac

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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







@[simp]
theorem mem_affineFamilyCommonZeroFinset
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) (x : ι → ZMod p) :
    x ∈ affineFamilyCommonZeroFinset p forms s ↔
      ∀ q ∈ s, (forms q).evalZMod p x = 0 := by
  simp [affineFamilyCommonZeroFinset]

















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
/-! ## Arbitrary finite-family intersection densities -/

open Wikipedia.SzemeredisTheorem in
/-- The product definition is the indicator of the simultaneous zero set. -/
theorem solution
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    affineFamilyZeroProduct p forms s =
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) := by
  classical
  funext x
  by_cases hx : ∀ q ∈ s, (forms q).evalZMod p x = 0
  · have hmem :
        x ∈ affineFamilyCommonZeroFinset p forms s := by
      exact (mem_affineFamilyCommonZeroFinset p forms s x).mpr hx
    rw [show
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) x = 1 by
        simp [finsetIndicator, hmem]]
    unfold affineFamilyZeroProduct
    apply Finset.prod_eq_one
    intro q hq
    have hqmem : x ∈ (forms q).zeroFinsetZMod p := by
      exact AffineForm.mem_zeroFinsetZMod p (forms q) x |>.mpr
        (hx q hq)
    simp [finsetIndicator, hqmem]
  · push Not at hx
    obtain ⟨q, hqs, hqzero⟩ := hx
    have hnotmem :
        x ∉ affineFamilyCommonZeroFinset p forms s := by
      intro hmem
      exact hqzero
        ((mem_affineFamilyCommonZeroFinset p forms s x).mp
          hmem q hqs)
    rw [show
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) x = 0 by
        simp [finsetIndicator, hnotmem]]
    unfold affineFamilyZeroProduct
    apply Finset.prod_eq_zero hqs
    have hqnotmem : x ∉ (forms q).zeroFinsetZMod p := by
      simpa using hqzero
    simp [finsetIndicator, hqnotmem]
