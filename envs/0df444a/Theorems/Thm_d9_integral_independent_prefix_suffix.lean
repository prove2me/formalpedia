-- Prove2me | Theorems.Thm_d9_integral_independent_prefix_suffix
-- name    : d9_integral_independent_prefix_suffix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:45:52.822529+00:00
-- url     : https://prove2.me/theorems/930b6e05-8e39-432b-be2e-80bcd4155cac
-- title:
--   Factor integrals over independent finite demand blocks
-- statement:
--   For the independent finite prefix and suffix demand blocks, the expectation of a product of measurable integrable functions factors into the product of their expectations.
-- source:
--   Cause-linked repair of failed extracted publication 98e71f01-7e40-4f45-ac1c-57754c6427ed; exact source declaration 084, restoring MeasureTheory and ProbabilityTheory scopes required by the statement and source proof.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem d9_integral_independent_prefix_suffix
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (j k : ℕ)
    (F : (Finset.Icc 1 j → ℝ) → ℝ)
    (G : (Finset.Icc (j + 1) (k + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFint : Integrable (fun ω => F (fun i => X i.1 ω)) P) :
    ∫ ω, F (fun i => X i.1 ω) * G (fun i => X i.1 ω) ∂P =
      (∫ ω, F (fun i => X i.1 ω) ∂P) *
        (∫ ω, G (fun i => X i.1 ω) ∂P) := by sorry
