-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_edge_lower_for_triangular_incidence_count
-- name    : WilliamsonShmoys.maximal_edge_lower_for_triangular_incidence_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:13:46.236858+00:00
-- url     : https://prove2.me/theorems/f2bcadcd-42d3-4cf2-b4cc-052a8cb334d1
-- title:
--   Maximal drawable supergraph attains the planar edge bound
-- statement:
--   If `X` is drawable and maximal among drawable graphs containing `W`, then for at least three vertices it has at least 3|V|−6 edges. The hypotheses retain both containment of `W` and the exact maximality condition. This removes the maximality-to-edge-count argument from the parent. A proof route establishes the standard structural properties of a maximal planar graph—connectivity and triangular faces—and counts edge-face incidences with Euler's formula. The core obligation is formalizing those properties for `HasPlanarDrawingOn`; no invalidated augmentation lemma is assumed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_edge_lower_for_triangular_incidence_count
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : forall u v, W.Adj u v -> X.Adj u v)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, W.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    3 * (Fintype.card V : Int) - 6 <= (X.edgeSet.ncard : Int) := by sorry
