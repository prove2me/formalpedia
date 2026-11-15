-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_log_two_div_four_mul_div_log_le_card
-- name    : Wikipedia.SzemeredisTheorem.eventually_log_two_div_four_mul_div_log_le_card
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:54:09.041663+00:00
-- url     : https://prove2.me/theorems/a2302109-031c-48ec-85ea-126cfb34775a
-- title:
--   A uniform asymptotic Chebyshev bound in quarter intervals
-- statement:
--   For every sufficiently large natural $X$, the number of primes in $(\lfloor X/4\rfloor,X]$ is at least
--
--   $$
--   \frac{\log2}{4}\frac{X}{\log X}.
--   $$
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/Chebyshev.lean#L212-L247

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Wikipedia.SzemeredisTheorem
open Finset Real
open Filter Asymptotics

theorem Wikipedia.SzemeredisTheorem.eventually_log_two_div_four_mul_div_log_le_card :
    ∀ᶠ X : ℕ in atTop,
      log 2 / 4 * X / log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by sorry
