-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:34.506505+00:00
-- url     : https://prove2.me/theorems/622c27aa-dbf7-499b-9813-a2a2eb387f09
-- title:
--   Selberg majorants attached to a structured smooth cutoff
-- statement:
--   A smooth sieve cutoff $\chi$ determines its own derivative-energy normalizer $c_\chi$. Its majorant at natural parameters $R,W,n$ is the normalized Selberg weight formed from the underlying real function $\chi$ and this normalizer:
--
--   $$
--   \nu_{\chi,R,W}(n)=\frac{\varphi(W)}{W}\,
--   \frac{\Lambda_{\chi,R}(n)^2}{c_\chi\log R}.
--   $$
--
--   For a positive cyclic modulus $N$ and residue shift $b$, the localized $W$-tricked version uses the existing short-interval majorant on $\mathbb Z/N\mathbb Z$, substituting the same cutoff function and normalizer. The bundle makes these structured substitutions explicit; the positivity and domination results are separate theorems.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothMajorant.lean#L20-L57

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
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
# The smooth cutoff instantiated in the Selberg majorant

This file connects `SmoothSieveCutoff` to the previously total divisor-sum
definitions.  The positivity of the cutoff normalizer discharges every
normalization side condition, including the exact value of the majorant on
primes beyond the sieve level.
-/

namespace Wikipedia.SzemeredisTheorem



/-- The structured cutoff version of the normalized Selberg majorant. -/
noncomputable def SmoothSieveCutoff.majorant
    (χ : SmoothSieveCutoff) (R W n : ℕ) : ℝ :=
  normalizedSelbergMajorant χ.toFun χ.normalizer R W n







/-- The localized W-tricked majorant associated to a structured cutoff. -/
noncomputable def SmoothSieveCutoff.wTrickedMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (n : ZMod N) : ℝ :=
  Wikipedia.SzemeredisTheorem.wTrickedMajorant
    χ.toFun χ.normalizer R W b n









end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.wTrickedMajorant.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


