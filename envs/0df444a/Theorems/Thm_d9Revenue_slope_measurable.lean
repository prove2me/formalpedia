-- Prove2me | Theorems.Thm_d9Revenue_slope_measurable
-- name    : d9Revenue_slope_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:18.933453+00:00
-- url     : https://prove2.me/theorems/a9d7eaa7-1f78-4bab-b443-18f70172cf22
-- title:
--   d9Revenue_slope_measurable
-- statement:
--   Automatically extracted helper theorem d9Revenue_slope_measurable from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_measurable_comp
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_slope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (k : ℕ) (s t : ℝ) :
    Measurable (fun ω =>
      slope (fun y => revenue f p (fun i => X i ω) k y) s t) := by sorry
