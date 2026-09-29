-- Prove2me | Theorems.Thm_unimodal_of_deriv_sign
-- name    : unimodal_of_deriv_sign
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T18:25:26.467186+00:00
-- url     : https://prove2.me/theorems/7b2cbc55-bbe0-476c-a625-aa174855365a
-- title:
--   Unimodality from a single sign change of the derivative
-- statement:
--   **Unimodality from a single-sign-change derivative (Siegel 2001, Theorem 2.1, p.5).** If $\varphi$ is differentiable everywhere with derivative $\varphi'$ that is positive on $(0,a)$ and negative on $(a,\mu)$ (a single interior maximum at $a$), then $\varphi$ is strictly increasing on $[0,a]$ and strictly decreasing on $[a,\mu]$. This is the derivative-sign half of unimodality, the step that turns the sign pattern of the log-density-difference derivative into the `StrictMonoOn`/`StrictAntiOn` hypotheses of the single-crossing lemma `unimodal_single_crossing`.
-- source:
--   A. Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, Theorem 2.1, p.5 (single interior turning point). Mathlib: strictMonoOn_of_hasDerivWithinAt_pos / strictAntiOn_of_hasDerivWithinAt_neg.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false
open Set

theorem unimodal_of_deriv_sign
    (φ φ' : ℝ → ℝ) (μ a : ℝ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x)
    (hneg : ∀ x ∈ Ioo a μ, φ' x < 0) :
    StrictMonoOn φ (Icc 0 a) ∧ StrictAntiOn φ (Icc a μ) := by sorry
