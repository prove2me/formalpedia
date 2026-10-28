-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_zero_divisor_pos
-- name    : ZeroFreeBridge.zeta_zero_divisor_pos
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:42:57.10149+00:00
-- url     : https://prove2.me/theorems/fcc62c61-d88e-4650-add8-5634ac4deb0f
-- title:
--   Positive multiplicity of a zeta zero in a pole-free ball
-- statement:
--   Let $R>0$, let $1$ lie outside the closed ball centered at $c$ with radius $R$,
--   and suppose $\operatorname{Re}c>1$. If $\rho$ is in the open ball and $\zeta(\rho)=0$,
--   then its divisor multiplicity in that ball satisfies
--   $$\operatorname{div}_{B(c,R)}\zeta(\rho)\ge1.$$
--   The ball avoids the pole at $1$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaZeroFree.lean#L26-L52

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- PHASE 4 (dVP frontier, the SELF-CONTAINED zero-free region): drop the multiplicity hypothesis.

   `dlvp_zeta_region_rate_effective` takes the zero's multiplicity `k` (with `1 ≤ k`) as input.
   `zeta_zero_divisor_pos` derives `1 ≤ divisor ζ (ball c₀ R) ρ₀` directly from `ζ ρ₀ = 0`
   (`analyticOrderAt ≥ 1` at a zero, finite because ζ is not locally zero on the connected disk —
   `ζ c₀ ≠ 0` at the centre `Re c₀ > 1`).  Feeding this in gives the fully self-contained region

     `riemannZeta_ne_zero_region` :  `55/16 ≤ |γ|` ∧ `1 - dlvpRateC/log|γ| < β`  ⟹  `ζ(β+iγ) ≠ 0`,

   i.e. `ζ(s) ≠ 0` on `Re s > 1 - dlvpRateC/log|Im s|` (for `|Im s| ≥ 55/16`), with `dlvpRateC` the
   EXPLICIT effective constant.  The `β ≥ 3/4` restriction of the rate theorem is discharged here:
   `dlvpRateC ≤ 1/1792` and `log|γ| ≥ 1`, so `1 - dlvpRateC/log|γ| > 3/4`, hence any zero in the
   region already has `β > 3/4`; and `β < 1` since ζ has no zeros with `Re ≥ 1`.

   conjecture1_proved = False (NOT a proof of RH — a kernel-verified reduction; it says a zero in the
   region cannot exist, which is what dVP gives, not a proof that ζ's zeros lie on the line).
-/




open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_zero_divisor_pos {c₀ ρ₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hc : 1 < c₀.re)
    (hρ : ρ₀ ∈ ball c₀ R) (hzero : riemannZeta ρ₀ = 0) :
    1 ≤ divisor riemannZeta (ball c₀ R) ρ₀ := by sorry
