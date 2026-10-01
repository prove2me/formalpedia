-- Prove2me | Theorems.Thm_syracuse_descent_new24_step14_chunk02_seven_mod32
-- name    : syracuse_descent_new24_step14_chunk02_seven_mod32
-- status  : Open
-- author  : @Sneed
-- created : 2026-10-01T08:03:12.193977+00:00
-- url     : https://prove2.me/theorems/61065a9b-db48-4dac-9043-7015cf6dd029
-- title:
--   Syracuse step-14 descent on chunk 2/5 at $2^{24}$
-- statement:
--   For any natural number whose residue modulo $2^{24}$ belongs to the named 678-element chunk, the accelerated Syracuse iterate $T^{14}(n)$ is strictly smaller than $n$. Every representative in this chunk has total stripped exponent $S=23$, with $S+1\le 24$ and $3^{14}<2^{23}$, so the fixed representative certificate transfers to the full residue class.
-- source:
--   Computational certificate child of the Prove2Me Collatz residual tree; uniformity theorem https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New24Step14Chunk02Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new24_step14_chunk02_seven_mod32 (n : ℕ)
    (h : n % 16777216 ∈ syracuseSevenMod32New24Step14Chunk02Classes) :
    syracuseStep^[14] n < n := by sorry
