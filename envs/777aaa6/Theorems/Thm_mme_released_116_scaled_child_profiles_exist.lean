-- Prove2me | Theorems.Thm_mme_released_116_scaled_child_profiles_exist
-- name    : mme_released_116_scaled_child_profiles_exist
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:31:57.891485+00:00
-- url     : https://prove2.me/theorems/924d992c-b400-4c26-9d00-59f7d630d6e5
-- title:
--   Every scaled released (1,1,6) profile has physical child words
-- statement:
--   For every nonnegative integer $k$, the released owner-zero $(1,1,6)$ component admits a common reference assignment with regional sizes $k n_r$ and exact split multiplicities $k m_r(c)$. In each mode $i$, there exists a physical child-word assignment with multiplicities
--   $$\mu_i^{(k)}(c,w)=k\mu_i(c,w),$$
--   and every assigned word has the grade of its reference cell. The three mode assignments share the reference; this statement does not assert that arbitrary choices of those words form a supported tensor triple. It supplies profile feasibility at all integer scales.
-- source:
--   Physical complementary cells and released (1,1,6) integer profile mass and support.

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false


open MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit

theorem mme_released_116_scaled_child_profiles_exist (k : ℕ) :
    ∃ a : RecursiveXHash.Address 4 6 parent (fun r => k * regionalSize r),
      a ∈ RecursiveXHash.target (fun r c => k * splitCount r c) ∧
      ∀ i : Fin 3, Nonempty (CellWord (fullCell parent_total a)
        (fun w : CompleteWord 2 => ∑ h, (w h).val)
        (fun c => (c.2.val i).val)
        (fun c w => k * integerProfile i c w)) := by sorry
