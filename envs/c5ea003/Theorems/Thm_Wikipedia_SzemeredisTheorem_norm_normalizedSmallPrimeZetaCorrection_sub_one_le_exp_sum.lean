-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
-- name    : Wikipedia.SzemeredisTheorem.norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:54.229238+00:00
-- url     : https://prove2.me/theorems/d5217ac4-b762-4e9a-ae40-3e97e5a4d50a
-- title:
--   A prime-sensitive exponential correction bound
-- statement:
--   Let $\kappa$ be finite with $m=|\kappa|$, let $R\ge2$ and $w\ge0$ be integers, and let $t,u\in\mathbb R^\kappa$. Assume $\delta\ge0$ bounds the distance from $1$ of both divisor phases at every frequency coordinate and every prime $p\le w$. Then
--   $$
--   \|Z^{\mathrm{small}}_{R,w}(t,u)-1\|\le
--   \exp\!\left(\sum_{p\le w}\left[\exp\!\left(\frac{12m\delta^2}{p}\right)-1\right]\right)-1.
--   $$
--   The sum is over primes and retains the contribution of each individual prime.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedEulerCorrectionLimit.lean#L365-L437

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## One paired phase -/
/-! ## A finite system at one prime -/
/-! ## Accumulation over the small primes -/

theorem Wikipedia.SzemeredisTheorem.norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q) - 1‖ ≤ δ)
    (huclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q) - 1‖ ≤ δ) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          (∑ p ∈ smallPrimeFinset w,
            (Real.exp
                ((Fintype.card κ : ℝ) *
                  (12 * δ ^ 2 / (p : ℝ))) -
              1)) -
        1 := by sorry
