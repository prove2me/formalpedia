-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_le_sieveMajorant_of_bounds
-- name    : Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_sieveMajorant_of_bounds
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:14.240302+00:00
-- url     : https://prove2.me/theorems/cd77a79d-7ded-436c-8ca5-56cdcbf943bc
-- title:
--   Global scale bounds give domination by the sieve majorant
-- statement:
--   Let $N\ne0$, $k\ge3$, $N\ge1$, $W>0$, and let $\chi$ be a smooth sieve cutoff. Assume $2\le\operatorname{sieveLevel}(k,N)<N/64$, $WN+b\le N^2$, and $(\operatorname{sieveExponent}(k)/2)\log N\le\log\operatorname{sieveLevel}(k,N)$. Then the W-tricked prime weight with scale $\operatorname{primeScale}(k,\chi.\mathrm{normalizer})$ is pointwise bounded by the smooth sieve majorant at that sieve level.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Majorization.lean#L171-L267

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Assembly-facing prime-weight majorization

The pointwise Selberg majorization theorem reduces its substantive case to
two scalar inequalities: the sieve level lies below the represented prime,
and the scaled logarithm of that prime is at most
`log R / χ.normalizer`.

This file derives both inequalities from global bounds that are independent
of the residue `n`.  The remaining eventual parameter argument only has to
establish those four global bounds for `R = sieveLevel k N`.
-/
open Wikipedia.SzemeredisTheorem
open Filter Real

theorem Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_sieveMajorant_of_bounds
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hN : 1 ≤ N)
    (hW : 0 < W)
    (hRtwo : 2 ≤ sieveLevel k N)
    (hRbelow : sieveLevel k N < N / 64)
    (hvalueUpper : W * N + b ≤ N ^ 2)
    (hlogLower :
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight
          (primeScale k χ.normalizer) W b n ≤
        χ.wTrickedMajorant (sieveLevel k N) W b n := by sorry
