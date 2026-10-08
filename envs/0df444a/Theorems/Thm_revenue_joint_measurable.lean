-- Prove2me | Theorems.Thm_revenue_joint_measurable
-- name    : revenue_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:36.102346+00:00
-- url     : https://prove2.me/theorems/8740cda5-a31f-4fc3-a1ab-73060fbc7d05
-- title:
--   revenue_joint_measurable
-- statement:
--   Automatically extracted helper theorem revenue_joint_measurable from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_joint_measurable (f p : ℕ → ℝ) :
    ∀ n, Measurable
      (fun z : (ℕ → ℝ) × ℝ => revenue f p z.1 n z.2) := by sorry
