-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
-- name    : GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:19.275677+00:00
-- url     : https://prove2.me/theorems/a5c7d947-191c-475e-99b9-940555daa689
-- title:
--   Primes in a quarter interval
-- statement:
--   For a natural number $X$, this finite set consists of primes $p$ satisfying
--
--   $$
--   \lfloor X/4\rfloor<p\le X.
--   $$
--
--   The upper endpoint is included and the lower endpoint is excluded. The quotient is natural-number division, so the definition also specifies the small and zero values of $X$ without additional assumptions. This is the prime sample used by the quarter-interval Chebyshev estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/Chebyshev.lean#L9-L11

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics

/-- The natural primes in the quarter interval `(X / 4, X]`. -/
def primesInQuarterInterval (X : ℕ) : Finset ℕ :=
  {p ∈ Finset.range (X + 1) | p.Prime ∧ X / 4 < p}































end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.primesInQuarterInterval.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


