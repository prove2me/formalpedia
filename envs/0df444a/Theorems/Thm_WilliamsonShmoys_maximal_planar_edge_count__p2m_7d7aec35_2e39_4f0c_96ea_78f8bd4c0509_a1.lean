-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:18:30.512992+00:00
-- url     : https://prove2.me/theorems/513f0e25-8b21-45bc-8db8-f06f4ba42a04
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   Every inclusion-maximal graph admitting the supplied crossing-free drawing on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges. This is the reusable maximal-planar edge-count theorem needed by the parent; its proof must establish the triangulation consequence of maximality and count incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
