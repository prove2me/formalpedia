-- Prove2me | Theorems.Thm_mme_regional_joint_potential_scale
-- name    : mme_regional_joint_potential_scale
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:36:16.980329+00:00
-- url     : https://prove2.me/theorems/66d65105-8aa8-4c06-8a0b-bf8feb71b567
-- title:
--   Regional joint entropy under integer replication
-- statement:
--   Replicating every split count by k multiplies the joint entropy potential by k, including zero replication and empty count entries.
-- source:
--   Entropy scaling for the released regional extraction: homogeneous mass entropy, invariant normalized parent mixtures, and fixed-tolerance losses.

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open MME.RegionRate
set_option autoImplicit false
universe u

theorem mme_regional_joint_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) :
    jointPotential (fun r c => k * m r c) = (k : ℝ) * jointPotential m := by sorry
