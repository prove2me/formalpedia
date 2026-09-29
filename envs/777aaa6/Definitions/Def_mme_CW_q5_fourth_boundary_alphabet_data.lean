-- Prove2me | Definitions.Def_mme_CW_q5_fourth_boundary_alphabet_data
-- name    : mme_CW_q5_fourth_boundary_alphabet_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-21T18:48:53.33813+00:00
-- url     : https://prove2.me/theorems/5287a423-2060-448a-b0b7-b3570fb60faa
-- title:
--   Canonical q=5 fourth boundary Z-alphabet sizes and logarithmic rate
-- statement:
--   The fiber-size table counts canonical fourth Z coordinates by total grade and left-square grade. Its rows are the products of square-grade dimensions 1,10,27,10,1. PositiveSize replaces empty fibers by 1 for logarithms; supported profiles give them zero weight. LogDimension is the entropy of the prescribed grade profile plus its average logarithmic alphabet size.
-- source:
--   Canonical fourth-power CW basis and prescribed Z profiles, q=5.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data
open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
open scoped BigOperators
set_option autoImplicit false
namespace MME.CWFourthBoundaryQ5
/-- Cardinalities of the canonical fourth Z-alphabet fibers, by total and left-square grade. -/
def fiberSize : Fin 9 → Fin 5 → ℕ :=
  ![![1,0,0,0,0], ![10,10,0,0,0], ![27,100,27,0,0],
    ![10,270,270,10,0], ![1,100,729,100,1], ![0,10,270,270,10],
    ![0,0,27,100,27], ![0,0,0,10,10], ![0,0,0,0,1]]
/-- Replace unused zero-size fibers by one when writing logarithmic expressions. -/
def positiveSize (k : Fin 9) (a : Fin 5) : ℕ := max 1 (fiberSize k a)
/-- Entropy and letter-choice rate for one exact prescribed Z profile. -/
noncomputable def logDimension (k : Fin 9) (p : IntegerZSplitProfile 5) : ℝ :=
  (∑ a, Real.negMulLog ((p.count a : ℝ) / p.denominator)) +
    ∑ a, ((p.count a : ℝ) / p.denominator) * Real.log (positiveSize k a)
end MME.CWFourthBoundaryQ5


