-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:19:55.742335+00:00
-- url     : https://prove2.me/theorems/e8b43d75-ed08-4724-804f-a24b9741c20c
-- title:
--   Three-state prime incidences in paired divisor families
-- statement:
--   At every active prime–form incidence of a support assignment, a three-state choice records whether the prime occurs in the left divisor, the right divisor, or both. The associated Fourier term is respectively minus the left phase, minus the right phase, or their product.
--
--   Products of the chosen distinct primes reconstruct a paired divisor family. A reverse assignment is recovered from left and right divisibility, with the expected inverse interpretation on the prescribed support fiber. The bundle supplies the product of all state phases, the finite-prime embedding into naturals, and the finite set of state assignments whose reconstructed divisors each lie between one and the sieve level $R$. These data retain the individual coordinate cutoffs used in the integral-cancellation argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalDivisorIntegralCancellation.lean#L84-L1082

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff





end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/

/-- For every incidence `q ∈ support p`, choose whether `p` occurs in the
left divisor, the right divisor, or both. -/
abbrev FixedFamilyPairedPrimeStateAssignment
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :=
  (p : {p // p ∈ P}) →
    ({q // q ∈ support p} → Fin 3)

/-- The phase contributed by one of the three nonempty paired states. -/
noncomputable def pairedFourierPrimeStateTerm
    (R p : ℕ) (t u : ℝ) (state : Fin 3) : ℂ :=
  if state = 0 then
    -SmoothSieveCutoff.divisorMultiplicativePhase R p t
  else if state = 1 then
    -SmoothSieveCutoff.divisorMultiplicativePhase R p u
  else
    SmoothSieveCutoff.divisorMultiplicativePhase R p t *
      SmoothSieveCutoff.divisorMultiplicativePhase R p u



/-- Product of all state phases belonging to one assignment. -/
noncomputable def fixedFamilyPairedPrimeStateTerm
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) : ℂ :=
  ∏ p : {p // p ∈ P},
    ∏ q : {q // q ∈ support p},
      pairedFourierPrimeStateTerm
        R (p : ℕ) (t q) (u q) (A p q)





/-! ## The squarefree divisor family encoded by a state assignment -/

noncomputable def fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) : Finset {p // p ∈ P} := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1

noncomputable def fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) : Finset {p // p ∈ P} := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0





/-- Multiply the selected distinct primes in the left and right
occurrences of every form. -/
noncomputable def fixedFamilyPairedPrimeStateDivisorFamily
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    κ → ℕ × ℕ :=
  fun q =>
    (∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
        (p : ℕ),
      ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
        (p : ℕ))































/-- Recover the three-state assignment of a paired divisor family from
prime divisibility.  On a support fiber every active incidence has at
least one of the two divisibilities. -/
noncomputable def fixedFamilyPairedPrimeStateAssignmentOf
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ) :
    FixedFamilyPairedPrimeStateAssignment support :=
  fun p q =>
    if (p : ℕ) ∣ (z q).1 then
      if (p : ℕ) ∣ (z q).2 then 2 else 0
    else 1





def fixedFamilyPrimeSubtypeNatEmbedding
    (P : Finset Nat.Primes) :
    {p // p ∈ P} ↪ ℕ where
  toFun p := (p : ℕ)
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact hpq







noncomputable def coordinatewiseAdmissiblePairedPrimeStateAssignments
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    Finset (FixedFamilyPairedPrimeStateAssignment support) :=
  Finset.univ.filter fun A =>
    fixedFamilyPairedPrimeStateDivisorFamily support A ∈
      smoothDivisorFamilyChoices κ R









/-! ## Fourier integration of one support fiber -/

















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.coordinatewiseAdmissiblePairedPrimeStateAssignments.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPairedPrimeStateLeftPrimes.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPairedPrimeStateRightPrimes.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedFourierPrimeStateTerm.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


