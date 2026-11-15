-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
-- name    : Wikipedia.SzemeredisTheorem.tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:43.752194+00:00
-- url     : https://prove2.me/theorems/74952c68-9142-4cb3-81b6-87c43f60dca5
-- title:
--   Joint-scale convergence of the normalized small-prime correction
-- statement:
--   Let $\kappa$ be finite and let $R_n,w_n$ be natural sequences, $T_n$ real, and $t_n,u_n$ real vectors indexed by $\kappa$. Assume eventually $R_n>1$, $w_n\ge2$, $T_n\ge0$, and every coordinate of $t_n,u_n$ has absolute value at most $T_n$. If $(w_n+1)\operatorname{cutoffPhaseMagnitudeBound}(R_n,w_n,T_n)^2\to0$, the normalized small-prime zeta correction at $(R_n,w_n,t_n,u_n)$ tends to $1$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedEulerCorrectionLimit.lean#L835-L959

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
/-! ## The actual cutoff phases -/
/-! ## Linearized control and joint convergence -/

theorem Wikipedia.SzemeredisTheorem.tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
    {κ : Type*} [Fintype κ]
    (R w : ℕ → ℕ) (T : ℕ → ℝ)
    (t u : ℕ → κ → ℝ)
    (hR : ∀ᶠ n in atTop, 1 < R n)
    (hw : ∀ᶠ n in atTop, 2 ≤ w n)
    (hT : ∀ᶠ n in atTop, 0 ≤ T n)
    (ht : ∀ᶠ n in atTop, ∀ q, |t n q| ≤ T n)
    (hu : ∀ᶠ n in atTop, ∀ q, |u n q| ≤ T n)
    (hscale :
      Tendsto
        (fun n =>
          (((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
                (R n) (w n) (T n) ^ 2))
        atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        normalizedSmallPrimeZetaCorrection
          (R n) (w n) (t n) (u n))
      atTop (𝓝 1) := by sorry
