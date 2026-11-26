-- Prove2me | Theorems.Thm_section5_normalize_perturbation
-- name    : section5_normalize_perturbation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:14.731328+00:00
-- url     : https://prove2.me/theorems/fc92e0ce-3b54-4639-bee4-9bcdb13f7253
-- title:
--   Perturbation bound for normalization in a real normed space
-- statement:
--   Let V be a real normed vector space and x,y∈V be nonzero. Then $$\left\|\frac x{\|x\|}-\frac y{\|y\|}\right\|\le\frac{2\|x-y\|}{\|y\|}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5Normalize.lean, lines 5–7.

import Mathlib
set_option autoImplicit false

theorem section5_normalize_perturbation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x-y‖ / ‖y‖ := by sorry
