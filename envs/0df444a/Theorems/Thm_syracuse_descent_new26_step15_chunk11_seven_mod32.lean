-- Prove2me | Theorems.Thm_syracuse_descent_new26_step15_chunk11_seven_mod32
-- name    : syracuse_descent_new26_step15_chunk11_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T11:42:26.682451+00:00
-- url     : https://prove2.me/theorems/1ed155a2-b2b5-41df-b277-939609ef2d81
-- title:
--   Syracuse step-15 descent on chunk 11/13 at $2^{26}$
-- statement:
--   For any natural number whose residue modulo $2^{26}$ belongs to the named 745-element chunk, the accelerated Syracuse iterate $T^{15}(n)$ is strictly smaller than $n$. Every representative in this chunk has total stripped exponent $S=25$, with $S+1\le 26$ and $3^{15}<2^{25}$, so the fixed representative certificate transfers to the full residue class.
-- source:
--   Computational certificate child of the Prove2Me Collatz residual tree; uniformity theorem https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New26Step15Chunk11Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new26_step15_chunk11_seven_mod32 (n : ℕ)
    (h : n % 67108864 ∈ syracuseSevenMod32New26Step15Chunk11Classes) :
    syracuseStep^[15] n < n := by sorry
