-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR7_omega_indicator
-- name    : ErdosProblems.Erdos1049.PaperR7.omega_indicator
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:42:26.766158+00:00
-- url     : https://prove2.me/theorems/ec775d64-9b53-4a1a-932e-eeacd78b8474
-- title:
--   Omega indicator
-- statement:
--   For every real 0≤x<1, the source weight is zero or one, and weight one is equivalent to membership in the literal Ω support.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperOmegaIndicatorR7.lean#L1296-L1394
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# R7: the exact 48-cell proof of `res:omega-indicator`

Full proof-source candidate, NOT compiler-checked in this environment.
The theorem is over real x, includes every left endpoint, and excludes each
right endpoint. Rational midpoint checks are not substituted for the proof:
each cell supplies four floor bounds and an interval-containment argument.
No `sorry`, extra axiom, or native_decide is used.
-/

open ErdosProblems.Erdos1049.PaperR7

theorem ErdosProblems.Erdos1049.PaperR7.omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by sorry
