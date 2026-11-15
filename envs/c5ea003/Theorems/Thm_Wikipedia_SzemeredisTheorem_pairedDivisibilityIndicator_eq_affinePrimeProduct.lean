-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityIndicator_eq_affinePrimeProduct
-- name    : Wikipedia.SzemeredisTheorem.pairedDivisibilityIndicator_eq_affinePrimeProduct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:09.381195+00:00
-- url     : https://prove2.me/theorems/2651d066-550f-4fc3-bdac-cb1a2afc29a8
-- title:
--   An affine-model divisibility indicator factors over primes
-- statement:
--   Let finite types $\kappa,\iota$ have decidable equality, and let $z$ be a squarefree paired-divisor choice with nonzero global LCM $D$. If the natural-valued functions on $(\mathbb Z/D\mathbb Z)^\iota$ satisfy the affine prime-model property, their paired divisibility indicator at each tuple is the product of the canonical affine paired prime factors evaluated at its prime-coordinate images.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PairedLocalFactors.lean#L624-L665

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
/-! ## Exact arbitrary-family local factor formula -/
/-! ## Localization of the canonical CRT factors -/

theorem Wikipedia.SzemeredisTheorem.pairedDivisibilityIndicator_eq_affinePrimeProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz)
    (x : ι → ZMod (pairedDivisorLcm z)) :
    pairedDivisibilityIndicator values z x =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affinePairedPrimeFactor forms z hz p
          (coordinatePrimePowerEquiv x p) := by sorry
