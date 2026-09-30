-- Prove2me | Theorems.Thm_Hirsch_exposed_core_edge_has_minkowski_bridge
-- name    : Hirsch.exposed_core_edge_has_minkowski_bridge
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T01:15:18.88235+00:00
-- url     : https://prove2.me/theorems/9265e218-624c-4c18-86a6-7406004fc14a
-- title:
--   An exposed finite-hull core edge lifts to a genuine Minkowski-sum edge
-- statement:
--   Let $S_0,\ldots,S_{m-1}$ be nonempty finite point sets in a real vector space, and let $P_i=\operatorname{conv}(S_i)$. Fix one core index $c$ and distinct listed points $u,v\in S_c$. Suppose a linear functional $f_0$ has equal values at $u,v$, bounds every point of $S_c$ from above by that value, and every maximizing listed point lies in $[u,v]$. These finite conditions certify that $[u,v]$ is the whole exposed core edge.
--
--   For the Minkowski sum $R=\sum_i P_i$, there exist a linear functional $f$, listed endpoints $a_i,b_i\in S_i$, and nonnegative scalars $\eta_i$, with $a_c=u$, $b_c=v$, $\eta_c=1$, such that
--
--   $$f(v-u)=0,\qquad b_i=a_i+\eta_i(v-u),\qquad P_i\cap\{f=f(a_i)\}=[a_i,b_i].$$
--
--   Writing $A=\sum_i a_i$ and $B=\sum_i b_i$, the endpoints are distinct, $f$ is bounded above on $R$ by $f(A)$, and
--
--   $$R\cap\{f=f(A)\}=[A,B],\qquad [A,B]\text{ is an extreme subset of }R.$$
--
--   Thus there is a genuine exposed edge of the sum whose core components are the specified endpoints $u,v$. The new functional and all component support segments are conclusions, not supplied certificates. Lower-dimensional factors, point factors, parallel edge directions and redundant listed points are allowed; neither full dimensionality nor simpliciality is assumed.
--
--   This supplies the edge-bridge existence step in Minkowski fibre routing. It does not choose a short core path, prove all abstract edges exposed without a supplied exposing functional, discover a decomposition of an unrelated H-polytope, or establish a uniform Hirsch diameter bound.
--
--   **Formalization Note** The result uses only Mathlib sets, convex hulls, segments, linear maps and `IsExtreme`. A nondegenerate segment that is an extreme subset is precisely the project's ordinary-edge adjacency predicate.
-- source:
--   Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643v1 (2018), Lemma 3.8, https://arxiv.org/html/1806.07643v1; DOI 10.4153/S0008439518000668. This is its exposed-core-edge forward direction with explicit simultaneous finite-factor supporting data. The quotient/finite-separation and perturbation proof is given in explanation.md and research/GENERIC_MINKOWSKI_EDGE_LIFT.md. It closes the core-edge existence gap recorded in section 3 of research/SIMULTANEOUS_MINKOWSKI_LIFT.md at 634e255ba0b83e31be98437159a4c65b377c7eca. No historical novelty claim.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.exposed_core_edge_has_minkowski_bridge
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (c : Fin m) (S : Fin m → Finset E) (hS : ∀ i, (S i).Nonempty)
    (u v : E) (hu : u ∈ S c) (hv : v ∈ S c) (huv : u ≠ v)
    (f₀ : E →ₗ[ℝ] ℝ) (h₀ : f₀ v = f₀ u)
    (hbound₀ : ∀ x ∈ S c, f₀ x ≤ f₀ u)
    (hmax₀ : ∀ x ∈ S c, f₀ x = f₀ u → x ∈ segment ℝ u v) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    ∃ (f : E →ₗ[ℝ] ℝ) (a b : Fin m → E) (η : Fin m → ℝ),
      f (v-u) = 0 ∧ a c = u ∧ b c = v ∧ η c = 1 ∧
      (∀ i, a i ∈ S i ∧ b i ∈ S i ∧ 0 ≤ η i ∧ b i = a i + η i • (v-u) ∧
        (∀ x ∈ S i, f x ≤ f (a i)) ∧
        {x | x ∈ convexHull ℝ (S i : Set E) ∧ f x = f (a i)} =
          segment ℝ (a i) (b i)) ∧
      (∑ i, a i) ≠ (∑ i, b i) ∧
      (∀ z ∈ R, f z ≤ f (∑ i, a i)) ∧
      {z | z ∈ R ∧ f z = f (∑ i, a i)} = segment ℝ (∑ i, a i) (∑ i, b i) ∧
      IsExtreme ℝ R (segment ℝ (∑ i, a i) (∑ i, b i)) := by sorry
