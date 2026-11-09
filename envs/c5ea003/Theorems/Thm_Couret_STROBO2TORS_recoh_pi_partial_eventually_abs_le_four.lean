-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_eventually_abs_le_four
-- name    : Couret.STROBO2TORS.recoh_pi_partial_eventually_abs_le_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:00.230962+00:00
-- url     : https://prove2.me/theorems/7787e939-6751-4ddd-87ea-fcb35a9935d7
-- title:
--   Rational pi centres eventually lie within four
-- statement:
--   For rational $x$, define $e_x(n)=x(x^2)^n/(1-x^2)$. Put $a_x(n)=\sum_{k<n}(-1)^kx^{2k+1}/(2k+1)$, $\pi_n=16a_{1/5}(n)-4a_{1/239}(n)$, $p_n=16e_{1/5}(n)+4e_{1/239}(n)$, $t_n=2\cdot8^n/n!$, and $E_{m,n}=2p_m+t_n$. All are rational and are interpreted as real where limits are stated. There exists a natural threshold after which
--
--   $$|\pi_n|\le4.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStablePrecision.lean#L52-L66, lines 52–66; source file SHA-256 75737fd29409c44da0d31022f86d5e77f03903b260a104075e16bef2fff8543d; theorem Couret.STROBO2TORS.recoh_pi_partial_eventually_abs_le_four

import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_error
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false

/-!
Existence of finite rational precision certificates for every positive error
budget.  These theorems concern the explicit error expressions checked by
the decoder.  They do not assert refinement of the Python precision-search
loop or of its JSON interface.
-/

namespace Couret.STROBO2TORS

open Filter Topology

theorem recoh_pi_partial_eventually_abs_le_four :
    ∀ᶠ n : ℕ in atTop, |recohPiPartial n| ≤ 4 := by sorry








end Couret.STROBO2TORS
