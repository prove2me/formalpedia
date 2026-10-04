-- Prove2me | Theorems.Thm_syracuse_descent_new23_step13_seven_mod32
-- name    : syracuse_descent_new23_step13_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T09:39:25.644976+00:00
-- url     : https://prove2.me/theorems/64328eb8-8ef8-45d2-af15-771013915f9a
-- title:
--   Syracuse descent at step 13 on 1570 new classes modulo $2^{23}$
-- statement:
--   Let $T$ be the accelerated Syracuse map. If $n$ belongs modulo $2^{23}$ to the named 1570-class certificate set, then the fixed iterate $T^{13}(n)$ is strictly smaller than $n$. Every canonical representative in this set has total stripped exponent $S=22$; the exact computation satisfies $S+1\le 23$ and $3^{13}<2^{22}$, so Terras uniformity transfers the representative descent to its complete residue class. This is a finite certificate leaf split from the hard residual branch.
-- source:
--   Derived from a4ee549a-031c-41b2-923c-b6e1d51bbc45 by exact residue refinement; Terras uniformity: https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New23Step13Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new23_step13_seven_mod32 (n : ℕ)
    (h : n % 8388608 ∈ syracuseSevenMod32New23Step13Classes) :
    syracuseStep^[13] n < n := by sorry
