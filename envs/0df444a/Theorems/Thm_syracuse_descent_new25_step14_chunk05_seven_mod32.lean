-- Prove2me | Theorems.Thm_syracuse_descent_new25_step14_chunk05_seven_mod32
-- name    : syracuse_descent_new25_step14_chunk05_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T09:17:51.534565+00:00
-- url     : https://prove2.me/theorems/3fcfb08e-bf28-4696-9a8c-30c0d87651a6
-- title:
--   Syracuse step-14 descent on chunk 5/5 at $2^{25}$
-- statement:
--   For any natural number whose residue modulo $2^{25}$ belongs to the named 677-element chunk, the accelerated Syracuse iterate $T^{14}(n)$ is strictly smaller than $n$. Every representative in this chunk has total stripped exponent $S=24$, with $S+1\le 25$ and $3^{14}<2^{24}$, so the fixed representative certificate transfers to the full residue class.
-- source:
--   Computational certificate child of the Prove2Me Collatz residual tree; uniformity theorem https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New25Step14Chunk05Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new25_step14_chunk05_seven_mod32 (n : ℕ)
    (h : n % 33554432 ∈ syracuseSevenMod32New25Step14Chunk05Classes) :
    syracuseStep^[14] n < n := by sorry
