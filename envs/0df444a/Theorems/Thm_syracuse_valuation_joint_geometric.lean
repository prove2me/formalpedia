-- Prove2me | Theorems.Thm_syracuse_valuation_joint_geometric
-- name    : syracuse_valuation_joint_geometric
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T07:20:32.903475+00:00
-- url     : https://prove2.me/theorems/6735c10b-38b9-4a49-838f-9480f5452a53
-- title:
--   Joint geometric approximation for Syracuse valuations
-- statement:
--   An explicit-constant probability-space formulation of Tao's Proposition 1.9: fix any c > 0 and residue-error constant K >= 0. There are A,d > 0, independent of the probability space, input law, modulus exponent q and prefix length t, such that the following holds. If N is measurable and almost surely a positive odd integer, q >= (2+c)t, and the unhalved atomwise L1 distance of N modulo 2^q from uniform odd residues is at most K/2^q, then the unhalved L1 distance of its first t exact Syracuse valuations from t independent positive geometric variables of mean 2 is at most A exp(-dt). The geometric law is explicitly extended to all natural-valued vectors by assigning mass 2^(-sum a_i) to vectors with all coordinates positive and zero otherwise. The empty-vector case is included. This is a joint valuation-law approximation, not global Collatz convergence or the almost-bounded logarithmic-density theorem. Source: Tao, Almost all orbits of the Collatz map attain almost bounded values, Proposition 1.9 and Section 4, https://arxiv.org/html/1909.03562v7 .

import Mathlib
import Definitions.Def_syracuseStep
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open Classical

theorem syracuse_valuation_joint_geometric (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ), Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) → ∀ q t : ℕ, (2 + c) * (t : ℝ) ≤ (q : ℝ) → (∑ r : Fin (2 ^ q), |(μ {ω : Ω | N ω % 2 ^ q = r.val}).toReal - (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) → (∑' a : Fin t → ℕ, |(μ {ω : Ω | ∀ i : Fin t, (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal - (if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0)|) ≤ A * Real.exp (-d * (t : ℝ)) := by sorry
