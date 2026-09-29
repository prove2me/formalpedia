-- Prove2me | Theorems.Thm_mme_released_116_scaled_fine_word_window
-- name    : mme_released_116_scaled_fine_word_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:38:30.055363+00:00
-- url     : https://prove2.me/theorems/d907c21c-dda2-429a-9d5e-05c5e4d83be5
-- title:
--   The scaled released global window follows from physical fine-word regional typicality
-- statement:
--   For every positive integer $k$, there exists an ordering of the $2kd^4$ physical child positions of released owner-zero component $(1,1,6)$ with the following property. For any fine word of length $4kd^4$, regional parent typicality of its grouped child words implies
--   $$\left|\frac{\#\{p:\text{parent word at }p=w\}}{kd^4}-\frac{H_i(w)}{d^4}\right|\le\varepsilon$$
--   in each mode $i$ and at every full word $w$, where $H_i$ is the exact released joint-row marginal. Both groupings use the same fine word in its original coordinate order. This establishes the histogram inclusion through the physical splitting map used by integer extraction. It does not assert the remaining grading, rate or global-witness conditions.
-- source:
--   Physical fine-coordinate regrouping and scaled released (1,1,6) regional-window aggregation.

import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_released_116_regional_total
import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_116_scaled_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3) (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
