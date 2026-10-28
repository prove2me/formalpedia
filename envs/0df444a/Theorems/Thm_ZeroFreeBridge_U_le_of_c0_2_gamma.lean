-- Prove2me | Theorems.Thm_ZeroFreeBridge_U_le_of_c0_2_gamma
-- name    : ZeroFreeBridge.U_le_of_c0_2_gamma
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:37.363285+00:00
-- url     : https://prove2.me/theorems/441ab766-3a6f-49d5-9aca-5c953fb4dc2a
-- title:
--   Explicit bound for a shifted-circle numerator
-- statement:
--   Let $0<R<3/2$, $|\gamma|\ge R+2$, and put $c=2+i\gamma$. Then
--   $$\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}\le2|\gamma|+11.$$
--   This bounds the geometric factor in the zeta boundary estimate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaAzeta.lean#L17-L40

import Mathlib
/- PHASE 4 (dVP frontier, item 2(ii) — Bg = O(L) via Aζ'' = O(log|γ|)): the sphere-oscillation
   constant `Aζ''` for the concrete centre `c₀ = 2+iγ` is O(log|γ|), so the entire-part bound
   `Bg = 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)²` (`norm_logDeriv_g_le_wired`) is O(L), `L = log|γ|` — the second
   O(L) input `hAL_concrete` consumes (`hBg`).

   Crux: `U'' = (‖c₀‖+R)/(|γ|-R) + (‖c₀‖+R)/(2-R) = O(|γ|)` (the 2nd term (‖c₀‖+R)/(2-R) dominates,
   since c₀.re=2 and R<3/2 ⟹ 2-R>1/2).  `U_le_of_c0_2_gamma`: `U'' ≤ 2|γ|+11` (‖c₀‖≤2+|γ| via
   `norm_add_le`; first term ≤ 7/2, second ≤ 2|γ|+15/2, by `div_le_iff₀` + `nlinarith`).
   `Azeta_le_of_c0_2_gamma`: `Aζ'' = log U'' - log(2-π²/6) ≤ log((2|γ|+11)/(2-π²/6))` (log monotone
   on the U'' bound + `Real.log_div`).  conjecture1_proved = False (NOT a proof of RH).
-/

open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.U_le_of_c0_2_gamma (γ R : ℝ) (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|) :
    (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
      + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R)
      ≤ 2 * |γ| + 11 := by sorry
