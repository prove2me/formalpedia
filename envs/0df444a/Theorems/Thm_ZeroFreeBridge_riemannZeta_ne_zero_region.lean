-- Prove2me | Theorems.Thm_ZeroFreeBridge_riemannZeta_ne_zero_region
-- name    : ZeroFreeBridge.riemannZeta_ne_zero_region
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:47:40.492303+00:00
-- url     : https://prove2.me/theorems/e79633a0-0e2a-49c3-9c20-a0111ece81ee
-- title:
--   Effective de la Vallée Poussin zero-free region
-- statement:
--   Let $\beta,\gamma\in\mathbb R$, with $|\gamma|\ge55/16$, and let
--   $C=\operatorname{dlvpRateC}$ be the defined effective constant. Then
--   $$\beta>1-\frac{C}{\log|\gamma|}\quad\Longrightarrow\quad
--   \zeta(\beta+i\gamma)\ne0.$$
--   This gives the zero-free region without a separate multiplicity assumption.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaZeroFree.lean#L54-L99

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_dlvp_zeta_region_rate_effective
import Theorems.Thm_ZeroFreeBridge_zeta_zero_divisor_pos
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

theorem ZeroFreeBridge.riemannZeta_ne_zero_region (β γ : ℝ)
    (hγ : 55/16 ≤ |γ|) (hβlow : 1 - dlvpRateC / Real.log |γ| < β) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0 := by sorry
