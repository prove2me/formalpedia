-- Prove2me | Theorems.Thm_d9LeftSlope_abs_le_fare_bound
-- name    : d9LeftSlope_abs_le_fare_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:40.993989+00:00
-- url     : https://prove2.me/theorems/7ae7096f-4881-4819-8935-b87b13479354
-- title:
--   d9LeftSlope_abs_le_fare_bound
-- statement:
--   Automatically extracted helper theorem d9LeftSlope_abs_le_fare_bound from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
open NestedSeatAlloc.IntPolicy

theorem d9LeftSlope_abs_le_fare_bound
    (f p x : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → |f i| ≤ M) →
      ∀ s, |d9LeftSlope f p x k s| ≤ M := by sorry
