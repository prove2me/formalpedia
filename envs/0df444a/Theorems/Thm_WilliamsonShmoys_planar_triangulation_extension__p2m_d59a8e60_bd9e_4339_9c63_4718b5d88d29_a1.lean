-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:29.757954+00:00
-- url     : https://prove2.me/theorems/4ae5175f-f6af-4329-a008-007eae5b47e6
-- title:
--   Planar triangulation extension with exact edge count
-- statement:
--   Any drawable finite simple graph on at least three vertices extends, on the same vertex type, to a drawable supergraph with exactly 3|V|−6 edges. For the parent, maximality forces that extension to equal K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        L.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
