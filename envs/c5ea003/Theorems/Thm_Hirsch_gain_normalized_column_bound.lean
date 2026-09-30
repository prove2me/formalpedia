-- Prove2me | Theorems.Thm_Hirsch_gain_normalized_column_bound
-- name    : Hirsch.gain_normalized_column_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T20:26:26.410044+00:00
-- url     : https://prove2.me/theorems/11190507-08f0-41de-b93b-9e620b6dd184
-- title:
--   Transport and cycle-gap bounds control a normalized inverse-column entry
-- statement:
--   Suppose a transported coordinate is at most Gamma times a positive root magnitude, while the normalization denominator is at least eta times that root magnitude. If Gamma is nonnegative and eta is positive, then the normalized coordinate is at most Gamma/eta. This is the scalar core of the gain-lattice inverse-column bound.
-- source:
--   Standalone Mathlib-only restatement of the gain-lattice normalization primitive developed in PR #210.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem Hirsch.gain_normalized_column_bound (x root denominator Gamma eta : ℝ)
    (hGamma : 0 ≤ Gamma) (heta : 0 < eta) (hroot : 0 < |root|)
    (htransport : |x| ≤ Gamma * |root|)
    (hgap : eta * |root| ≤ |denominator|) :
    |x / denominator| ≤ Gamma / eta := by sorry
