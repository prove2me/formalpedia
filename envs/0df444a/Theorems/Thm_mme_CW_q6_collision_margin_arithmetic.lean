-- Prove2me | Theorems.Thm_mme_CW_q6_collision_margin_arithmetic
-- name    : mme_CW_q6_collision_margin_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:12:40.257793+00:00
-- url     : https://prove2.me/theorems/ad22d70d-cc41-4593-b3d0-8edd41985c9b
-- title:
--   The q=6 concentration and collision shares leave a strict retained-fiber margin
-- statement:
--   Let B,M,X,D,R,Q,S,Z be nonnegative integers. Assume the modulus dominates the collision coordinate count, the lower-tail gap is large enough, the per-destroyed-fiber deletion cost is large enough, and Q uses at most one sixteenth of the raw shared-Z incidence: $$4X^2\le M,\qquad16BM\le R^2,\qquad5B\le8MD,\qquad16MQ\le SZ.$$ Then $$M^3DR^2Q+2R^2ZBX^2S+2DBM^3SZ\le DR^2M^2SZ.$$ Quantitatively, the baseline, concentration error, and collision terms consume at most 1/16, 1/8, and 4/5 of the available mass, totaling 79/80. This is the strict arithmetic margin needed by the eventually-large q=6 same-parameter averaging argument.
-- source:
--   Arithmetic normalization of the CW90 q=6 affine-hash concentration and ordered collision estimates

import Mathlib

set_option autoImplicit false

theorem mme_CW_q6_collision_margin_arithmetic
    {B M X D R Q S Z : ℕ}
    (hXM : 4 * X ^ 2 ≤ M)
    (hRmargin : 16 * B * M ≤ R ^ 2)
    (hDmargin : 5 * B ≤ 8 * M * D)
    (hQ : 16 * M * Q ≤ S * Z) :
    M ^ 3 * D * R ^ 2 * Q +
          R ^ 2 * (2 * Z * B * X ^ 2 * S) +
          D * (2 * B * M ^ 3 * S * Z) ≤
        D * R ^ 2 * M ^ 2 * S * Z := by
  sorry
