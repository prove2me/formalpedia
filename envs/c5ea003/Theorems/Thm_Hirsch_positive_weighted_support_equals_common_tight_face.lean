-- Prove2me | Theorems.Thm_Hirsch_positive_weighted_support_equals_common_tight_face
-- name    : Hirsch.positive_weighted_support_equals_common_tight_face
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:13:43.48939+00:00
-- url     : https://prove2.me/theorems/3cfebe9d-22b9-4d64-825c-677300325c1f
-- title:
--   A positive weighted sum of supporting inequalities exposes exactly their common tight face
-- statement:
--   Let finitely many linear functionals be bounded above on a set P by values b_i, and give every row a strictly positive weight w_i. A point of P attains the weighted sum of all upper bounds if and only if it attains every individual upper bound. Hence the supporting face exposed by the positive weighted sum is exactly the common tight face of all the component inequalities.
-- source:
--   Standalone proof extracted from PR #210 support-intersection work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/positive_weighted_common_face/solution.lean

import Mathlib
open Set
open scoped BigOperators

theorem Hirsch.positive_weighted_support_equals_common_tight_face
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (P : Set E) (a : ι → E →ₗ[ℝ] ℝ) (b w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hb : ∀ i, ∀ x ∈ P, a i x ≤ b i) :
    {x : E | x ∈ P ∧ (∑ i, w i * a i x) = (∑ i, w i * b i)} =
      {x : E | x ∈ P ∧ ∀ i, a i x = b i} := by sorry
