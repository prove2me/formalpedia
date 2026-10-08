-- Prove2me | Theorems.Thm_eq30_revenue_measurable_comp
-- name    : eq30_revenue_measurable_comp
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T01:08:15.212078+00:00
-- url     : https://prove2.me/theorems/5fa05d66-306d-416b-9aed-e106469eb545
-- title:
--   eq30_revenue_measurable_comp
-- statement:
--   Automatically extracted helper theorem eq30_revenue_measurable_comp from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_revenue_measurable_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => revenue f p (fun i => X i ω) k (s ω)) := by sorry
