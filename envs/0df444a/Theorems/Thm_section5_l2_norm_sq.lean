-- Prove2me | Theorems.Thm_section5_l2_norm_sq
-- name    : section5_l2_norm_sq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:15.45428+00:00
-- url     : https://prove2.me/theorems/68adf075-b37d-5319-a392-eb33c7184dde
-- title:
--   Squared norm of a complex square-integrable function
-- statement:
--   Let $(X,\mathcal F,\mu)$ be a measure space and let $f:X\to\mathbb C$ belong to $L^2(\mu)$. Its equivalence class $[f]$ satisfies
--
--   $$
--   \|[f]\|_{L^2(\mu)}^2=\int_X|f(x)|^2\,d\mu(x).
--   $$
--
--   This connects the norm of a function-space vector with its scalar squared-amplitude integral.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5ProductSampling.lean, section5_l2_norm_sq, lines 11–24.

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem section5_l2_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by sorry
