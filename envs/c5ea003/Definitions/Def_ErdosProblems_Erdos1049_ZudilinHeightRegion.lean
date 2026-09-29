-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
-- name    : ErdosProblems_Erdos1049_ZudilinHeightRegion
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:44:58.082926+00:00
-- url     : https://prove2.me/theorems/931840ae-56ff-4dce-bdf4-608261a308c2
-- title:
--   Erdős #1049: elementary height-region certificates
-- statement:
--   Exact integer and logarithmic inequalities place 31/4 and its powers in the 81/200 height region while locating 3/2 outside it and the Bundschuh–Väänänen region. The submitted module contains the source declarations ZudilinHeightRegion, thirtyoneFour_power_certificate, thirtyoneFour_log_ratio_lt_eightyOne_twoHundredths, thirtyoneFour_mem_zudilinHeightRegion, zudilinHeightRegion_pow, among others. Source topic: Erdős #1049: elementary height-region certificates.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L20-L141
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #1049: elementary height-region certificates

Define the height region by
`log b / log a < 81 / 200`.  Exact integer and logarithmic inequalities place
`31 / 4` and all its positive powers inside this region, place `31 / 4`
outside the Bundschuh--Väänänen region, and place `3 / 2` outside both.

These are elementary parameter inequalities.  No hypergeometric asymptotic or
irrationality theorem is imported as an axiom.  Membership becomes useful only
after a separate analytic theorem is applied, while failure of membership is
method inapplicability and proves neither rationality nor irrationality.
-/

namespace ErdosProblems.Erdos1049

/-- The parameter region cut out by the single inequality
`log b / log a < 81 / 200`; no analytic hypotheses are included. -/
def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200

























end ErdosProblems.Erdos1049


