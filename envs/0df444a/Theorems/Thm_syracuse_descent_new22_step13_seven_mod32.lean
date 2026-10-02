-- Prove2me | Theorems.Thm_syracuse_descent_new22_step13_seven_mod32
-- name    : syracuse_descent_new22_step13_seven_mod32
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T07:39:08.245372+00:00
-- url     : https://prove2.me/theorems/b0d40471-1d4f-472f-a60c-ba085d48a6df
-- title:
--   Syracuse descent at step 13 on 1570 new classes modulo $2^{22}$
-- statement:
--   Let $T$ be the accelerated Syracuse map. If $n$ belongs modulo $2^{22}$ to the named 1570-class certificate set, then the fixed iterate $T^{13}(n)$ is strictly smaller than $n$. Every canonical representative in this set has total stripped exponent $S=21$; the exact computation satisfies $S+1\le 22$ and $3^{13}<2^{21}$, so Terras uniformity transfers the representative descent to its complete residue class. This is a finite certificate leaf split from the hard residual branch.
-- source:
--   Derived from 9e6f9691-d939-47a4-a212-468d00588765 by exact residue refinement; Terras uniformity: https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New22Step13Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_new22_step13_seven_mod32 (n : ℕ)
    (h : n % 4194304 ∈ syracuseSevenMod32New22Step13Classes) :
    syracuseStep^[13] n < n := by sorry
