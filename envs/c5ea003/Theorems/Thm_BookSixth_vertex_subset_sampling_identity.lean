-- Prove2me | Theorems.Thm_BookSixth_vertex_subset_sampling_identity
-- name    : BookSixth.vertex_subset_sampling_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:15:56.17985+00:00
-- url     : https://prove2.me/theorems/61aad6e7-9db7-4c9f-84c0-b82c7bf6f09e
-- title:
--   Exact vertex-subset survival weight under independent sampling
-- statement:
--   Let T be a subset of N labeled vertices and let p be real. For each Boolean vertex selection x, give it weight w(x), the product of p for each selected vertex and 1-p for each unselected vertex. Then
--
--   $$\sum_{x:\,T\subseteq x} w(x)=p^{|T|}.$$
--
--   For 0 ≤ p ≤ 1 this is the probability that every vertex of T survives independent retention. The polynomial identity also holds for all real p. It supplies the two-endpoint and four-endpoint survival factors in the crossing-lemma sampling argument, including empty T and the boundary probabilities.
-- source:
--   Algebraic intermediate for BookSixth.drawing_sampling_bound (6968bb2a-7af8-400f-bc59-39aa35d6ea0d). Derived directly from Mathlib Fintype.prod_sum, Mathlib/Algebra/BigOperators/Ring/Finset.lean lines 300-302 at c5ea00351c28e24afc9f0f84379aa41082b1188f: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/BigOperators/Ring/Finset.lean#L300-L302. Fix factors for vertices in T and sum the remaining factors p+(1-p)=1. This is a derived finite-product identity, not a separately numbered book result.

import Mathlib
open scoped BigOperators

theorem BookSixth.vertex_subset_sampling_identity {N : ℕ} (T : Finset (Fin N)) (p : ℝ) :
    (∑ x : Fin N → Bool,
      if ∀ v ∈ T, x v = true then
        ∏ v : Fin N, if x v then p else 1-p
      else 0) = p^T.card := by sorry
