-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:08.169172+00:00
-- url     : https://prove2.me/theorems/b36e4a06-e569-4990-9a06-8a34b4fc8586
-- title:
--   Extend a drawable graph to the planar edge bound
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly `3n − 6` edges. This removes the planar extension, triangulation, and edge-count argument from the parent. A proof route is to choose a maximal drawable supergraph, show it is triangulated, and apply Euler’s formula and face-edge counting. For three vertices, extension to the triangle handles the boundary case directly. Formalizing those steps for the supplied drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V), K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (hLdec : DecidableRel L.Adj),
        L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
