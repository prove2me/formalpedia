-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_gapped_re_complete
-- name    : XORFullTilt.Hardness.gapped_re_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:54:55.669436+00:00
-- url     : https://prove2.me/theorems/e5b8f7d3-5b41-4f84-ba59-cdf2e5d2a398
-- title:
--   Theorem 4.2 — constant-gap RE-completeness
-- statement:
--   For every fixed real $\varepsilon$ with $0<\varepsilon<10^{-8}$, the promise problem
--   $$\mathrm{TXOR}^{*}_{3/4-\varepsilon,\,3/4-10^{-8}}$$
--   is RE-complete under total computable promise-preserving reductions. For a finite effective tilted-game input, YES means $\omega^*(G)\ge3/4-\varepsilon$ and NO means $\omega^*(G)<3/4-10^{-8}$; the middle band is unpromised. An RE separator contains every YES input and no NO input. Every RE language on binary strings has a total computable reduction taking members to YES games and nonmembers to NO games.
--
--   The quantum value is the actual Born-rule supremum over all finite-dimensional complex tensor-product POVM strategies. There is no dimension bound, attained-optimum assumption, classical or tracial restriction, or hypothesis supplying a hard family or a gap-preserving reduction. The thresholds are fixed real parameters outside the machine input. This includes the full headline quantifiers and explicit source constant, together with the RE upper bound.
--
--   Differences from the source:
--   - encoding: finite effective explicit descriptions of tilted games → natural-number codes of integer-multiplicity rational tables with total default decoding; reason: every rational law is representable and the conversions are computable; semantic laws in the analytical lemmas remain arbitrary real laws
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.20, Theorem 4.2 and explicit-constant paragraph; p.4, Main Theorem

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_EffectiveGames

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Theorem 4.2, p.20, with p.4's headline quantifiers and p.20's explicit constants.
    Values range over every finite dimension and arbitrary tensor-product POVMs. -/
theorem gapped_re_complete (ε : ℝ) (hε : 0 < ε) (hsmall : ε < (1/100000000 : ℝ)) :
    PromiseREComplete (fun n => explicitValue n ≥ (3/4 : ℝ)-ε)
      (fun n => explicitValue n < (3/4 : ℝ)-(1/100000000 : ℝ)) := by sorry

end XORFullTilt.Hardness
