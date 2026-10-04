-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapInjectivity_quartic_is_proper
-- name    : ZetaNine.CoefficientMapInjectivity.quartic_is_proper
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T17:12:58.588126+00:00
-- url     : https://prove2.me/theorems/ca673a47-8c42-4909-8ab2-9384503415ec
-- title:
--   Every rational quartic multiplier lies in the strict proper domain
-- statement:
--   For every natural $n$, including zero, and every $W\in\mathbb Q[X]$ with natural degree at most four, $$2n+2\deg W<9(n+1).$$ Thus every rational quartic multiplier satisfies the strict proper-degree condition for the complete local-array injectivity result. Strict properness gives only at most order $1/t$ decay, without analytic summability or stronger asymptotic cancellation. At $n=0$, $W=X^4$ meets this condition and the actual weighted rational function is $1/t$ on its regular domain, so a simple pole remains possible.
-- source:
--   Zeta(9) finite proper-domain local coefficient-array research: missions/zeta9/research/coefficient-map-injectivity-2026-10-03.md. Frozen actual Lean source missions/zeta9/formalization/CoefficientMapInjectivity.lean, SHA256 ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095; uses genuine Base/Jet products and formal local jets. This concerns the complete (n+1) by 9 array, not the original five aggregated F outputs. Original declaration lines 228–230.

import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.quartic_is_proper (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) : ProperMultiplier n W:= by sorry
