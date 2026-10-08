-- Prove2me | Theorems.Thm_d9RightSlope_measurable
-- name    : d9RightSlope_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:19.944301+00:00
-- url     : https://prove2.me/theorems/3730e6cc-dbca-4e5e-8b29-fbf14730fb04
-- title:
--   d9RightSlope_measurable
-- statement:
--   Automatically extracted helper theorem d9RightSlope_measurable from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9RightSlope
open NestedSeatAlloc.IntPolicy

theorem d9RightSlope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => d9RightSlope f p (fun i => X i ω) k (s ω)) := by sorry
