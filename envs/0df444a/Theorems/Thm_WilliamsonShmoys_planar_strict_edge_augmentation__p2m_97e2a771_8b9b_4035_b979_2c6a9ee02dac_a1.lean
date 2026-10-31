-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1
-- name    : WilliamsonShmoys.planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:17.031477+00:00
-- url     : https://prove2.me/theorems/671e5c30-1b1f-403c-8a8b-f487cd0d141b
-- title:
--   Strict planar edge augmentation below the maximal edge count
-- statement:
--   For a drawable simple graph on at least three vertices, if its edge count is strictly below 3|V|−6, there is a proper simple-graph supergraph on the same vertex set that still has a planar drawing. This constructive augmentation step removes the topological work from the parent; independently, prove it by taking a maximal drawable supergraph over the finite set of candidate graphs, then using component connection, face triangulation, and Euler’s formula to rule out a sparse maximal graph. The strict inequality and the lower bound of three vertices are needed, including at the three-vertex boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H ≠ M ∧ HasPlanarDrawingOn H := by sorry
