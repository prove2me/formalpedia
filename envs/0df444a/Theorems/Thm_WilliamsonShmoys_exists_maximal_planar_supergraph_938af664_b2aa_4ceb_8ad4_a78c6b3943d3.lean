-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:27:40.492879+00:00
-- url     : https://prove2.me/theorems/293f63a0-5dd3-4f06-81cd-21234e97dccf
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Extend the given planar graph to an inclusion-maximal planar graph on the same finite vertex type, without decreasing its edge count. A proof can maximize edge count among the finitely many simple graphs on V that contain G and admit the specified drawing; any proper planar supergraph would contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
