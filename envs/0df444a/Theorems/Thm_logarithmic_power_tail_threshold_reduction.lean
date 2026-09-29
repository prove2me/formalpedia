-- Prove2me | Theorems.Thm_logarithmic_power_tail_threshold_reduction
-- name    : logarithmic_power_tail_threshold_reduction
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T02:40:25.994315+00:00
-- url     : https://prove2.me/theorems/2d9c3905-e033-4928-b80c-6eb8664ab67b
-- title:
--   Uniform logarithmic-power tails imply negligible diverging-threshold exceptions
-- statement:
--   Let D be a domain of natural-number inputs, w nonnegative real weights, and P a real-valued quantity on inputs. Suppose there are positive constants C and c such that, for every integer threshold M and cutoff x at least two, the logarithmically normalized weighted mass of inputs satisfying P(n) > M is at most C/(log M)^c. Then for every real-valued f tending to infinity, the normalized weighted mass of inputs satisfying P(n) ≥ f(n) tends to zero. No monotonicity of f is required. The proof fixes a threshold, separates a finite initial segment, and lets its contribution vanish. This abstract reduction assumes the uniform tail bound; it does not prove that bound for Collatz or Syracuse orbits.
-- source:
--   Generalized finite-prefix deduction underlying Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 3: Theorem 3.1 to Theorem 1.6. https://arxiv.org/html/1909.03562v7 . This formalization abstracts the domain and nonnegative weights and uses integer cutoffs; it is not a claim that Tao states this generalization verbatim.

import Mathlib
import Definitions.Def_weightedLogMass
open Filter
open scoped Topology

theorem logarithmic_power_tail_threshold_reduction (D : ℕ → Prop) (w P f : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (hbound : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x → weightedLogMass D (fun k => (M : ℝ) < P k) w x ≤ C / Real.rpow (Real.log (M : ℝ)) c) (hf : Tendsto f atTop atTop) : Tendsto (fun cutoff : ℕ => weightedLogMass D (fun k => P k ≥ f k) w cutoff) atTop (𝓝 0) := by sorry
