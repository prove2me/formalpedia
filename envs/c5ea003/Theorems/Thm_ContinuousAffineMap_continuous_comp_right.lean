-- Prove2me | Theorems.Thm_ContinuousAffineMap_continuous_comp_right
-- name    : ContinuousAffineMap.continuous_comp_right
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:07:14.036004+00:00
-- url     : https://prove2.me/theorems/d795aa6b-86dc-4116-9e42-ede6af03ee52
-- title:
--   Precomposition of continuous affine maps is continuous
-- statement:
--   Precomposition by a fixed continuous affine map is continuous (Lipschitz with constant norm+1). Full type names avoid exotic notation.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Normed/Affine/ContinuousAffineMap.lean#L11-L12

import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace ContinuousAffineMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem continuous_comp_right (g : ContinuousAffineMap ℝ E F) :
    Continuous (fun f : ContinuousAffineMap ℝ F G ↦ f.comp g) := by sorry

end ContinuousAffineMap
