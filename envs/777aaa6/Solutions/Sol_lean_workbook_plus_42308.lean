-- Prove2me | solution 1 for lean_workbook_plus_42308
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:34.095063+00:00
-- url     : https://prove2.me/submissions/0c36327a-b193-48f4-94fe-1f62abd46a95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c u v : ℝ} (ha : a ≥ 0) (hb : b = a + u) (hc : c = a + u + v) (hu : u ≥ 0) (hv : v ≥ 0) : a^4 * (351 * u^2 + 351 * u * v + 351 * v^2) + a^3 * (900 * u^3 + 1350 * u^2 * v + 1458 * u * v^2 + 504 * v^3) + a^2 * (972 * u^4 + 1944 * u^3 * v + 2484 * u^2 * v^2 + 1512 * u * v^3 + 378 * v^4) + a * (488 * u^5 + 1220 * u^4 * v + 1892 * u^3 * v^2 + 1618 * u^2 * v^3 + 778 * u * v^4 + 160 * v^5) + (92 * u^6 + 276 * u^5 * v + 511 * u^4 * v^2 + 562 * u^3 * v^3 + 396 * u^2 * v^4 + 161 * u * v^5 + 27 * v^6) ≥ 0 := by
  (intros; positivity)
