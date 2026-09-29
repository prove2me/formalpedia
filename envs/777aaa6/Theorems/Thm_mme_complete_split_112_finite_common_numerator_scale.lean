-- Prove2me | Theorems.Thm_mme_complete_split_112_finite_common_numerator_scale
-- name    : mme_complete_split_112_finite_common_numerator_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T11:18:34.620977+00:00
-- url     : https://prove2.me/theorems/da592815-f24f-456e-b292-9a49482bcaa1
-- title:
--   Common scales for finitely many exact 112 profiles
-- statement:
--   Let $q>0$ and let $S$ be a finite set of natural numerators satisfying $882n<100q$. For each $n\in S$, the exact 112 profile parameter is $p=n/q$. Then for every positive tolerance $\delta$, all sufficiently large integers $m$ give one common base scale $N=qm$ at which every profile in $S$ has an actual coupled primary-hash family with counts $L=2nm$ and $G=(q-2n)m$. Each family has positive outer count, at most $4^N$ components per star, and the established outer-star and joint-star entropy lower bounds at tolerance $\delta$. The profile witnesses may depend on $n$, while the scale threshold is shared across the finite set. The endpoint $n=0$ is included.
-- source:
--   Finite intersection of the Lean-kernel-proved theorem mme_complete_split_112_parametric_canonical_directional_rates (https://prove2.me/theorems/ceb8e859-d3a2-4251-bd53-929f26f9b934), environment 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e. The profile range is the established hashing condition 341*l < 100*g after l=2*n and g=q-2*n; the result supplies a common compatible scale for finite optimizer tables used in the q=5, fourth-power construction of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5-7.

import Theorems.Thm_mme_complete_split_112_parametric_canonical_directional_rates

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

set_option autoImplicit false

theorem mme_complete_split_112_finite_common_numerator_scale (q : ℕ) (hq : 0 < q) (S : Finset ℕ) (hS : ∀ n ∈ S, 882 * n < 100 * q) (delta : ℝ) (hdelta : 0 < delta) : ∀ᶠ m : ℕ in atTop, ∀ n ∈ S, ∃ beta : Fin 3 → Profile 2, (∀ mode sigma, (beta mode).probability sigma = (profileProbability (((2 * n : ℕ) : ℚ) / (2 * (q : ℚ))) mode sigma : ℝ)) ∧ ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily (q * m) ((2 * n) * m) ((q - 2 * n) * m) A H, 0 < A ∧ H ≤ 4 ^ (q * m) ∧ ((2 * (q * m) : ℕ) : ℝ) * (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤ Real.log (A : ℝ) ∧ ((2 * (q * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤ Real.log ((A : ℝ) * (H : ℝ)) := by sorry
