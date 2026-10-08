-- Prove2me | Theorems.Thm_d9LeftSlope_measurable
-- name    : d9LeftSlope_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:13.28281+00:00
-- url     : https://prove2.me/theorems/8205fa13-4e48-4535-885a-2d562f86ccb9
-- title:
--   d9LeftSlope_measurable
-- statement:
--   Automatically extracted helper theorem d9LeftSlope_measurable from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
open NestedSeatAlloc.IntPolicy

theorem d9LeftSlope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => d9LeftSlope f p (fun i => X i ω) k (s ω)) := by sorry
