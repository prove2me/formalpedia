-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_densityTarget_le_primeScale_mul_log_div
-- name    : Wikipedia.SzemeredisTheorem.densityTarget_le_primeScale_mul_log_div
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:10.357325+00:00
-- url     : https://prove2.me/theorems/b4a51991-346c-4fcd-a861-e666ab3cb17c
-- title:
--   The density target fits below the prime-scale Chebyshev reserve
-- statement:
--   For a natural progression length $k\ge3$ and any positive real cutoff normalizer $c$, the prescribed density target and prime scale satisfy
--
--   $$
--   \delta(k,c)\le\alpha(k,c)\frac{\log2}{128}.
--   $$
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Parameters.lean#L117-L135

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/
open Wikipedia.SzemeredisTheorem
open Filter Real

theorem Wikipedia.SzemeredisTheorem.densityTarget_le_primeScale_mul_log_div
    {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    densityTarget k cutoffNormalizer ≤
      primeScale k cutoffNormalizer * log 2 / 128 := by sorry
