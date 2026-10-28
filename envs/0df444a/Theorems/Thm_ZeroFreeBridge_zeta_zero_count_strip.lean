-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_zero_count_strip
-- name    : ZeroFreeBridge.zeta_zero_count_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:01.320712+00:00
-- url     : https://prove2.me/theorems/7d4e6df5-6276-4560-b745-f2a9d1ad273d
-- title:
--   Explicit divisor count for a disk crossing the strip
-- statement:
--   Let $c\in\mathbb C$ and $r,R\in\mathbb R$ satisfy
--   $0<|r|<|R|$, $\operatorname{Re}c>1$,
--   $|R|<\operatorname{Re}c-1/2$, and $|R|+2\le|\operatorname{Im}c|$.
--   Put
--   $$U=\frac{|c|+|R|}{|\operatorname{Im}c|-|R|}
--   +\frac{|c|+|R|}{\operatorname{Re}c-|R|}.$$
--   Then the finite-support divisor sum of $\zeta$ on $\overline{B(c,|r|)}$ obeys
--   $$\sum{}^{\!f}_{u}\operatorname{div}_{\overline{B(c,|r|)}}\zeta(u)
--   \le\frac{\log(U/|\zeta(c)|)}{\log(R/r)}.$$
--   The real logarithm and division use Lean's total definitions for all real inputs.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaCountStrip.lean#L60-L89

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_zeta_sphere_bound_strip
/- PHASE 4 (dVP frontier, item 3 input — strip-capable Jensen zero count): the version of
   `zeta_zero_count_unconditional` (`DlvpZetaDisk`) that survives the disk DIPPING BELOW `Re = 1`.

   The count `∑ divisor ≤ log(M/‖ζ c‖)/log(R/r)` (`zeta_zero_count_le`) takes the boundary bound `M`
   as a HYPOTHESIS and only needs `1 < c.re` at the CENTER plus `1 ∉ closedBall c |R|` — ζ is
   analytic on ANY disk avoiding `s = 1`, even one reaching `Re < 1`.  The original
   `zeta_zero_count_unconditional` supplies `M` via `zeta_sphere_bound` (`Re > 1`), forcing
   `|R| + 1 < c.re`.  Here we supply `M` via `zeta_strip_bound` (valid on the FULL strip
   `Re > 0`, `s ≠ 1`), so the disk may enclose a nontrivial zero `ρ₀` (`Re < 1`).

   This delivers the `O(L)` zero-count bound `∑ |divisor| ≤ Ccount·L` that `hAL_arith` (`DlvpHALArith`)
   consumes.  conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_zero_count_strip (c : ℂ) (r R : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hc1 : 1 < c.re)
    (hRlt : |R| < c.re - 1/2) (himc : |R| + 2 ≤ |c.im|) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (((‖c‖ + |R|) / (|c.im| - |R|) + (‖c‖ + |R|) / (c.re - |R|)) / ‖riemannZeta c‖)
          / Real.log (R / r) := by sorry
