-- Prove2me | Theorems.Thm_syracuse_descent_new25_step15_chunk07_seven_mod32
-- name    : syracuse_descent_new25_step15_chunk07_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T09:18:10.391044+00:00
-- url     : https://prove2.me/theorems/32060ee9-2f10-4ef4-9854-c258ca25b81b
-- title:
--   Syracuse step-15 descent on chunk 7/13 at $2^{25}$
-- statement:
--   For any natural number whose residue modulo $2^{25}$ belongs to the named 745-element chunk, the accelerated Syracuse iterate $T^{15}(n)$ is strictly smaller than $n$. Every representative in this chunk has total stripped exponent $S=24$, with $S+1\le 25$ and $3^{15}<2^{24}$, so the fixed representative certificate transfers to the full residue class.
-- source:
--   Computational certificate child of the Prove2Me Collatz residual tree; uniformity theorem https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New25Step15Chunk07Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new25_step15_chunk07_seven_mod32 (n : ℕ)
    (h : n % 33554432 ∈ syracuseSevenMod32New25Step15Chunk07Classes) :
    syracuseStep^[15] n < n := by sorry
