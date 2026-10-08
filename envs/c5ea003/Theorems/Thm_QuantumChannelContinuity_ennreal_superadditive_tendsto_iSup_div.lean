-- Prove2me | Theorems.Thm_QuantumChannelContinuity_ennreal_superadditive_tendsto_iSup_div
-- name    : QuantumChannelContinuity.ennreal_superadditive_tendsto_iSup_div
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T18:23:44.796832+00:00
-- url     : https://prove2.me/theorems/973ed0f1-80be-456e-aabc-3f16ea8f70e5
-- title:
--   Fekete convergence for nonnegative extended-real superadditive sequences
-- statement:
--   Let $f:\mathbb{N}\to[0,+\infty]$ satisfy $f(m)+f(n)\le f(m+n)$ for every pair of natural numbers $m,n$. Then the normalized sequence converges in the extended nonnegative real line:
--
--   $$\lim_{n\to\infty}\frac{f(n)}{n}=\sup_{k\ge1}\frac{f(k)}{k}.$$
--
--   The assertion includes an infinite supremum and sequences with an infinite term. Nonnegativity and superadditivity imply monotonicity of $f$; this controls the infinite-value case, while the finite-value case reduces to the real subadditive Fekete theorem. This result identifies the regularized divergence defined by a positive-block supremum with the normalized block limit.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ExtendedFekete.lean#L31-L90

import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Instances.ENNReal.Lemmas
/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Fekete's lemma with infinite values retained

Nonnegative superadditive block quantities converge after normalization to
their positive-block supremum, whether that supremum is finite or infinite.
-/

open Filter Set
open scoped ENNReal Topology
namespace QuantumChannelContinuity
end QuantumChannelContinuity
open QuantumChannelContinuity

theorem QuantumChannelContinuity.ennreal_superadditive_tendsto_iSup_div (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) :
    Tendsto (fun n : ℕ => f n / (n : ℝ≥0∞)) atTop
      (𝓝 (⨆ n : ℕ, ⨆ (_ : 0 < n), f n / (n : ℝ≥0∞))):= by sorry
