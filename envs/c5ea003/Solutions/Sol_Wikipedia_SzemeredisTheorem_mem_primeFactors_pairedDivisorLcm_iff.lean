-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mem_primeFactors_pairedDivisorLcm_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:10.182753+00:00
-- url     : https://prove2.me/submissions/b4535002-239e-4148-be07-15da594697d7

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
/-- The prime support of the global paired LCM is the union of the prime
supports of its per-form local moduli. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) (p : ℕ) :
    p ∈ (pairedDivisorLcm z).primeFactors ↔
      p.Prime ∧ (pairedPrimeSupport z p).Nonempty := by
  have hD0 : pairedDivisorLcm z ≠ 0 :=
    (squarefree_pairedDivisorLcm hz).ne_zero
  rw [Nat.mem_primeFactors_of_ne_zero hD0]
  constructor
  · rintro ⟨hp, hpD⟩
    have hpProd :
        p ∣ ∏ q, pairedLocalModulus z q :=
      hpD.trans (by
        rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
        exact Finset.lcm_dvd_prod Finset.univ
          (pairedLocalModulus z))
    obtain ⟨q, _hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff
        (pairedLocalModulus z)).mp hpProd
    exact ⟨hp, ⟨q, by simp [hpq]⟩⟩
  · rintro ⟨hp, ⟨q, hq⟩⟩
    rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
    exact ⟨hp, (mem_pairedPrimeSupport z p q).mp hq |>.trans
      (Finset.dvd_lcm (f := pairedLocalModulus z)
        (Finset.mem_univ q))⟩
