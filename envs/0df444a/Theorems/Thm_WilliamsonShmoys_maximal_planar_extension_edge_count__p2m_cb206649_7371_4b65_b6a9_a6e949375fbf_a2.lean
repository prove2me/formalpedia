-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:13.950802+00:00
-- url     : https://prove2.me/theorems/89582c96-c588-4663-9e82-ebaf767d7a60
-- title:
--   Triangulated extension of a drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. The child packages the planar augmentation, triangulation, and edge count needed by the parent. Its boundary case |V|=3 is consistent: the extension can be K3, with three edges. A proof route is to maximize the number of edges among drawable supergraphs, show that maximality forces a connected triangulation, and apply Euler’s formula. This removes the geometric extension and counting argument from the parent; those remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
          3 * Fintype.card V - 6 = L.edgeFinset.card)) := by sorry
