-- Prove2me | Theorems.Thm_mme_CW_q6_eventual_threshold_choice
-- name    : mme_CW_q6_eventual_threshold_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:29:49.604812+00:00
-- url     : https://prove2.me/theorems/73aa7214-3644-446d-9b2d-66371ce7210a
-- title:
--   Explicit eventually-large q=6 thresholds satisfy every concentration and collision margin
-- statement:
--   Let B,M,S,Z be nonnegative integers with M>0 and 400M≤B. Define $$K=\left\lfloor\frac{3B}{4M}\right\rfloor,\quad H=\left\lfloor\frac{B}{8M}\right\rfloor,\quad R=\left\lfloor\frac B4\right\rfloor,\quad Q=\left\lfloor\frac{SZ}{16M}\right\rfloor.$$ Then R>0, H≤K, MK+R≤B, and the three strict-budget margins hold: $$16BM\le R^2,\qquad5B\le8M(K-H+1),\qquad16MQ\le SZ.$$ These are explicit integer thresholds for the eventually-large q=6 affine-hash concentration and X/Y-collision argument.
-- source:
--   Explicit floor-normalized threshold choice for the CW90 q=6 affine-hash argument

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_eventual_threshold_choice
    {B M S Z : ℕ} (hM : 0 < M) (hlarge : 400 * M ≤ B) :
    let K := (3 * B) / (4 * M)
    let H := B / (8 * M)
    let R := B / 4
    let Q := (S * Z) / (16 * M)
    0 < R ∧
      H ≤ K ∧
      M * K + R ≤ B ∧
      16 * B * M ≤ R ^ 2 ∧
      5 * B ≤ 8 * M * (K - H + 1) ∧
      16 * M * Q ≤ S * Z := by
  sorry
