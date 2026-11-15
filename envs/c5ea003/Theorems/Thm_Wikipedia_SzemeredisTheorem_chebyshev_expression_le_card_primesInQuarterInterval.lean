-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_chebyshev_expression_le_card_primesInQuarterInterval
-- name    : Wikipedia.SzemeredisTheorem.chebyshev_expression_le_card_primesInQuarterInterval
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:49:46.803159+00:00
-- url     : https://prove2.me/theorems/a8a4db58-f209-4b36-8220-99d7739583f3
-- title:
--   An explicit Chebyshev lower bound for primes in a quarter interval
-- statement:
--   For a natural $X\ge2$, let $P_X$ be the primes in $(\lfloor X/4\rfloor,X]$. Then
--
--   $$
--   \frac{X\log2-\log(X+1)-2\sqrt X\log X
--   -\lfloor X/4\rfloor\log4}{\log X}
--   \le |P_X|.
--   $$
--
--   The quarter cutoff uses natural division.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/Chebyshev.lean#L89-L113

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

theorem Wikipedia.SzemeredisTheorem.chebyshev_expression_le_card_primesInQuarterInterval
    {X : ℕ} (hX : 2 ≤ X) :
    (((X : ℝ) * log 2 - log (X + 1) -
          2 * √(X : ℝ) * log X) -
        log 4 * (X / 4 : ℕ)) /
      log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by sorry
