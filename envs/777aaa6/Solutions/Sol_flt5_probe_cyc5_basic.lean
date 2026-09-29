-- Prove2me | solution 1 for flt5_probe_cyc5_basic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:42:46.994443+00:00
-- url     : https://prove2.me/submissions/97b1565e-e439-4a11-8761-aa28c6cd9ddf

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem solution : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 := by
  haveI : IsCyclotomicExtension ({5} : Set ℕ) ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact ⟨IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ),
    IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)⟩
