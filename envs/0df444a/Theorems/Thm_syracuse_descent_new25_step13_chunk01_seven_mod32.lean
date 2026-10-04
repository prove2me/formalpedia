-- Prove2me | Theorems.Thm_syracuse_descent_new25_step13_chunk01_seven_mod32
-- name    : syracuse_descent_new25_step13_chunk01_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T09:17:32.473985+00:00
-- url     : https://prove2.me/theorems/866d5ac1-a93d-4f97-aabc-fcf12a0353b9
-- title:
--   Syracuse step-13 descent on chunk 1/2 at $2^{25}$
-- statement:
--   For any natural number whose residue modulo $2^{25}$ belongs to the named 785-element chunk, the accelerated Syracuse iterate $T^{13}(n)$ is strictly smaller than $n$. Every representative in this chunk has total stripped exponent $S=24$, with $S+1\le 25$ and $3^{13}<2^{24}$, so the fixed representative certificate transfers to the full residue class.
-- source:
--   Computational certificate child of the Prove2Me Collatz residual tree; uniformity theorem https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New25Step13Chunk01Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new25_step13_chunk01_seven_mod32 (n : ℕ)
    (h : n % 33554432 ∈ syracuseSevenMod32New25Step13Chunk01Classes) :
    syracuseStep^[13] n < n := by sorry
