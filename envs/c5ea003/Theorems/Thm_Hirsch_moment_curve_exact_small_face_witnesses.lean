-- Prove2me | Theorems.Thm_Hirsch_moment_curve_exact_small_face_witnesses
-- name    : Hirsch.moment_curve_exact_small_face_witnesses
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T00:35:56.03031+00:00
-- url     : https://prove2.me/theorems/d8214487-c5aa-446b-8e75-f485979b94f3
-- title:
--   Construct exact original-H witnesses for every small moment-curve face
-- statement:
--   For any finite injectively parametrized family of real moment points in dimension 2k, and any proper selected label subset S of cardinality at most k, construct a positive squared-root-polynomial average h and a vector x in R^(2k). Every mean-centered original moment-row inequality at x has exact slack product_{s in S}(a_i-a_s)^2/h. In particular all original inequalities hold and equality holds exactly at the selected labels. The only inputs are the injective parameter map, k, S, and its size/properness bounds: no support, feasible witness, rank, or extremal-point oracle is assumed. The empty subset and k=0 are included when the parameter type is nonempty. This supplies the constructive proper-subset side of the cyclic-family application of accepted #281; it does not establish infeasibility of the larger candidate sets, the entire exponential obstruction, full-dimensionality, or Polynomial Hirsch.
-- source:
--   Classical moment-curve neighborliness via squared-root polynomials, formalized directly against explicit mean-centered H inequalities. Project context: jjoshua2/prove2me-work #267 and accepted #281. Uses Mathlib polynomial evaluation, monic degree and finite-sum lemmas at the committed pin; no novelty or full conjecture claim.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem moment_curve_exact_small_face_witnesses {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : Function.Injective a) (k : ℕ) (S : Finset ι)
    (hS : S.card ≤ k) (hproper : S.card < Fintype.card ι) :
    ∃ h : ℝ, 0 < h ∧
      h = (∑ i, ∏ s ∈ S, (a i - a s) ^ 2) / (Fintype.card ι : ℝ) ∧
      ∃ x : Fin (2 * k) → ℝ, ∀ i : ι,
        (∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) =
          1 - (∏ s ∈ S, (a i - a s) ^ 2) / h ∧
        (∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) ≤ 1 ∧
        ((∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) = 1 ↔ i ∈ S) := by sorry
end Hirsch
