-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
-- name    : ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:21.927971+00:00
-- url     : https://prove2.me/theorems/6102498c-5129-4dc3-ad7b-ff8a5248ad8d
-- title:
--   R7: the exact 48-cell proof of `res:omega-indicator`
-- statement:
--   Each of 48 floor cells is checked at its inclusive left and exclusive right boundary to identify the exact source cyclotomic indicator. The submitted module contains the source declarations omegaWeight, InOmegaSupport, floor_from_bounds, omega_cell_00, omega_cell_01, among others. Source topic: R7: the exact 48-cell proof of `res:omega-indicator`.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperOmegaIndicatorR7.lean#L17-L1394
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

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

namespace ErdosProblems.Erdos1049.PaperR7

noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))

/-- Exactly the thirteen half-open intervals printed in the long record. -/
def InOmegaSupport (x : ℝ) : Prop :=
  ((1 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 12) ∨
  ((1 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 6) ∨
  ((3 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 4) ∨
  ((2 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 3) ∨
  ((5 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 5) ∨
  ((3 : ℝ) / 7 ≤ x ∧ x < (7 : ℝ) / 15) ∨
  ((1 : ℝ) / 2 ≤ x ∧ x < (8 : ℝ) / 15) ∨
  ((4 : ℝ) / 7 ≤ x ∧ x < (3 : ℝ) / 5) ∨
  ((9 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 3) ∨
  ((5 : ℝ) / 7 ≤ x ∧ x < (11 : ℝ) / 15) ∨
  ((11 : ℝ) / 14 ≤ x ∧ x < (4 : ℝ) / 5) ∨
  ((6 : ℝ) / 7 ≤ x ∧ x < (13 : ℝ) / 15) ∨
  ((13 : ℝ) / 14 ≤ x ∧ x < (14 : ℝ) / 15)





































































































end ErdosProblems.Erdos1049.PaperR7


