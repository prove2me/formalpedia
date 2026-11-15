-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:06:50.48204+00:00
-- url     : https://prove2.me/theorems/6e498282-7b7b-44d7-ab96-e7812cbd7019
-- title:
--   Finite small-prime corrections for the primorial W-trick
-- statement:
--   Let $W$ be the primorial at a natural parameter $w$, and let $P_w$ be the finite subtype of primes at most $w$. The small-prime correction is the product over $p\in P_w$ of the inverses of the cutoff zeta-system local factors.
--
--   The reduced-residue density is $\varphi(W)/W$, viewed as a complex number. For a family of $m$ paired forms, the unshifted zeta-system factor at a natural modulus $p$ is $(1-p^{-1})^m$. The normalized small-prime correction multiplies the finite correction by $(\varphi(W)/W)^m$, inserting the actual Selberg normalization explicitly.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedEulerCorrection.lean#L25-L383

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Mathlib.NumberTheory.PrimeCounting
import Lean
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The finite Euler correction at W-tricked primes

For `W = primorial w`, every arithmetic local factor at a prime `p ≤ w`
is one.  Relative to the universal zeta Euler model, its arithmetic/zeta
ratio is therefore the inverse zeta factor.  This file packages the exact
finite product of those inverses and compares it with the Selberg
normalization `(φ(W) / W)^m`.

The comparison is exact: the normalized correction is a finite product of
the ratios between the unshifted local model `(1 - p⁻¹)^m` and the shifted
Fourier-zeta local model.  Thus the only remaining small-prime asymptotic is
to show that these finitely many shifted model factors approach their
unshifted values in the chosen joint `w, R` regime.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



/-- Natural primes at most `w`, represented in the prime subtype used by
unordered Euler products. -/
def smallPrimeFinset (w : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE w).attach.map
    ⟨fun p =>
        (⟨p.1, Nat.prime_of_mem_primesLE p.2⟩ :
          Nat.Primes),
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun r : Nat.Primes => (r : ℕ)) hpq⟩









/-- The exact finite small-prime correction supplied by the zeta model. -/
noncomputable def smallPrimeZetaCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ p ∈ smallPrimeFinset w,
    (cutoffZetaEulerLocalFactor R t u p)⁻¹





/-! ## The parallel first-order correction -/









/-! ## Exact comparison with the totient normalization -/

/-- The density of reduced residues for the standard primorial W-trick,
viewed in `ℂ`. -/
noncomputable def primorialReducedResidueDensity (w : ℕ) : ℂ :=
  ((primorial w).totient : ℂ) / (primorial w : ℂ)



/-- The unshifted zeta local factor for a system of `m` paired forms. -/
noncomputable def unshiftedZetaSystemLocalFactor
    (m p : ℕ) : ℂ :=
  (1 - (p : ℂ)⁻¹) ^ m









/-! ## The unshifted phase model -/











/-- The finite correction after inserting the actual Selberg
normalization `(φ(W)/W)^m`. -/
noncomputable def normalizedSmallPrimeZetaCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  primorialReducedResidueDensity w ^ Fintype.card κ *
    smallPrimeZetaCorrection R w t u







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.normalizedSmallPrimeZetaCorrection.eq_1,
    `Wikipedia.SzemeredisTheorem.primorialReducedResidueDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.smallPrimeFinset.eq_1,
    `Wikipedia.SzemeredisTheorem.smallPrimeZetaCorrection.eq_1,
    `Wikipedia.SzemeredisTheorem.unshiftedZetaSystemLocalFactor.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


