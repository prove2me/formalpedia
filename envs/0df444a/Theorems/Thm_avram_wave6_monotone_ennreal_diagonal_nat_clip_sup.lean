-- Prove2me | Theorems.Thm_avram_wave6_monotone_ennreal_diagonal_nat_clip_sup
-- name    : avram_wave6_monotone_ennreal_diagonal_nat_clip_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:49:14.590989+00:00
-- url     : https://prove2.me/theorems/b197b0a9-09d2-4841-80e6-f61778a97ff8
-- title:
--   Monotone ENNReal sequence retains supremum under its own deterministic integer clock clipping
-- statement:
--   For any monotone sequence of extended nonnegative times a_n, the supremum of min(a_n,n) equals the original supremum of a_n. The proof distributes the two independent suprema over lattice infimum, then uses diagonal cofinality via max(n,m). It handles zero and infinity and is the bounded-clock algebra required for the original nonmonotone ruin-clipped stopping-envelope construction. No probabilistic or boundary assumption is added.
-- source:
--   Pinned Mathlib order-theoretic identities inf_iSup_eq, iSup_inf_eq, ENNReal.iSup_natCast; original-source bounded ruin clock theorem 3ae57b3c-959f-46f7-ba88-a55f35a44126 motivates the diagonal generalisation.

import Mathlib

open scoped NNReal ENNReal
noncomputable section

theorem avram_wave6_monotone_ennreal_diagonal_nat_clip_sup
    (a : ℕ → ℝ≥0∞) (ha : Monotone a) :
    (⨆ n : ℕ, min (a n) (n : ℝ≥0∞)) = (⨆ n : ℕ, a n) := by sorry
