-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- name    : WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:47.785192+00:00
-- url     : https://prove2.me/theorems/36faa255-a29b-4fd0-89f8-f64de761af4d
-- title:
--   Straight segments give valid individual edge arcs
-- statement:
--   For an edge with distinct placed endpoints, its affine segment is continuous and injective on the closed unit interval and has the required endpoint values. If the endpoints exhaust the vertices, the segment’s open interior avoids every vertex point: equality with either endpoint would contradict injectivity on the closed interval. Prove continuity coordinatewise, use injectivity of `p` and `u < v` for segment injectivity, and use endpoint equations plus injectivity for interior avoidance. This packages the geometric obligation for each edge; the parent handles the crossing condition separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (p : V -> Prod Real Real) (hp : Function.Injective p) (u v : V)
    (huv : u < v) (hvertices : forall w : V, Or (w = u) (w = v)) :
    And (ContinuousOn (fun t : Real => (1 - t) • p u + t • p v) (Set.Icc 0 1))
      (And (Set.InjOn (fun t : Real => (1 - t) • p u + t • p v) (Set.Icc 0 1))
        (And ((fun t : Real => (1 - t) • p u + t • p v) 0 = p u)
          (And ((fun t : Real => (1 - t) • p u + t • p v) 1 = p v)
            (forall t : Real, Set.Ioo (0 : Real) 1 t -> forall w : V,
              Not ((fun t : Real => (1 - t) • p u + t • p v) t = p w))))) := by
  sorry
