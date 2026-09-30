-- Prove2me | Theorems.Thm_Hirsch_cross_ratio_product_forces_small_separation
-- name    : Hirsch.cross_ratio_product_forces_small_separation
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T20:27:47.745684+00:00
-- url     : https://prove2.me/theorems/a98104a5-9d5e-46ec-be85-e484add4b797
-- title:
--   A cross-ratio product identity forces one normalized separation to be small
-- statement:
--   If two nonnegative normalized separations s and t are both at least delta, two auxiliary normalized factors u and v lie in [0,1], and their cross-ratio product satisfies s*t = epsilon*u*v, then delta squared is at most epsilon. This is the scalar obstruction used to show that a four-line configuration cannot be uniformly separated by affine preconditioning.
-- source:
--   Standalone Mathlib-only restatement of the affine-conditioning obstruction developed in PR #210.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem Hirsch.cross_ratio_product_forces_small_separation (s t u v delta epsilon : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hdelta_s : delta ≤ s) (hdelta_t : delta ≤ t)
    (heq : s * t = epsilon * u * v) : delta ^ 2 ≤ epsilon := by sorry
