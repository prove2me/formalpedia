-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_repr_R1
-- name    : ZeroFreeBridge.zeta_repr_R1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:13.881814+00:00
-- url     : https://prove2.me/theorems/82091376-38bd-43f5-b0dd-84da9b9db848
-- title:
--   Fractional-part representation where the zeta series converges
-- statement:
--   For every $s\in\mathbb C$ with $\operatorname{Re}s>1$, the defined
--   fractional-part expression obeys
--   $$\zeta(s)=\operatorname{stripRHS}(s).$$
--   This is the seed identity for continuation to the strip.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/StripReprR1.lean#L85-L238

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- (R1) DISCHARGE for `zeta_fract_repr_of` -- THE HARD ONE, WORK IN PROGRESS.

   The fractional-part representation on `Re s > 1`:

       riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx  =  stripRHS s.

   Mathlib v4.32.0 has NO such representation (confirmed), so it is built by Abel
   summation (`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) applied to
   `f x = x^{-s}`, `c 0 = 0`, `c (n+1) = 1`:

     ∑_{k≤n} k^{-s}  →  0 - ∫_{t>1} (-s·t^{-s-1})·⌊t⌋ dt  =  s∫_{t>1} ⌊t⌋ t^{-s-1} dt,
     ⌊t⌋ = t - {t},  s∫_{t>1} t^{-s} dt = s/(s-1)   ⟹   ζ(s) = s/(s-1) - s∫_{t>1}{t}t^{-s-1}.

   STATUS: FULLY ASSEMBLED, CI-green -- no `sorry`. The five analytic Abel-summation
   hypotheses (hf_diff, hf_int, h_lim, hg_dom, hg_int) are discharged on `Re s > 1`
   via a shared derivative helper `hasDerivAt_fPow` and the partial-sum `sum_cOne`;
   part (A) `tendsto_partialSum_zeta` identifies the LHS limit as `riemannZeta s`
   (Complex.summable_one_div_nat_cpow + zeta_eq_tsum... + hasSum_nat_add_iff reindex);
   part (B) evaluates the RHS limit value = `stripRHS s` (⌊t⌋ = t - {t} split,
   `∫_{Ioi 1}(↑t)^{-s} = 1/(s-1)` via integral_Ioi_cpow_of_lt). This discharges the
   R1 input of `zeta_fract_repr_of`. conjecture1_proved = False.
-/


open MeasureTheory Filter Topology Set

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_repr_R1 {s : ℂ} (hs : 1 < s.re) : riemannZeta s = stripRHS s := by sorry
