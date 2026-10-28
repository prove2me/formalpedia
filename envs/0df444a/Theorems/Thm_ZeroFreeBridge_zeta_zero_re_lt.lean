-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_zero_re_lt
-- name    : ZeroFreeBridge.zeta_zero_re_lt
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:08.582453+00:00
-- url     : https://prove2.me/theorems/e89e201c-2eec-4b5d-a3a6-5e946b6ef25c
-- title:
--   A nonzero zeta divisor lies left of a line beyond one
-- statement:
--   Let $\sigma>1$, let $1$ lie outside the closed ball $\overline B(c,R)$, and
--   let $\rho\in B(c,R)$. If the zeta divisor at $\rho$ in that ball is nonzero, then
--   $$\operatorname{Re}\rho<\sigma.$$
--   This confines the ball's zero support to the left of any line beyond $1$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaZeroLoc.lean#L15-L34

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- PHASE 4 (dVP frontier, item 4 — zero location): every ζ-zero in the disk has `Re < σ` (`σ > 1`),
   which discharges the `hother`/`hlt` hypotheses of `dlvp_zeta_region_of_canonical_decomp`.

   A point `ρ` in the divisor support of ζ is a zero (`divisor ≠ 0` ⟹ `analyticOrderAt ≠ 0` ⟹ `ζ ρ = 0`,
   using `AnalyticOnNhd.divisor_apply` + `apply_eq_zero_of_analyticOrderAt_ne_zero`), and ζ has no zeros
   with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`), so `Re ρ < 1 < σ`.  conjecture1_proved = False.
-/



open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_zero_re_lt {c₀ ρ : ℂ} {R σ : ℝ} (hσ : 1 < σ)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hρ : ρ ∈ ball c₀ R)
    (hdiv : divisor riemannZeta (ball c₀ R) ρ ≠ 0) :
    ρ.re < σ := by sorry
