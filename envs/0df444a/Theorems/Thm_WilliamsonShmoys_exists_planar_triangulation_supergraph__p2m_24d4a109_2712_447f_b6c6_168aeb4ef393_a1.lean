-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:42.338934+00:00
-- url     : https://prove2.me/theorems/c11f1659-d0fc-4751-a84f-f498781343a5
-- title:
--   Planar triangulation completion on the same vertex set
-- statement:
--   Every finite drawable simple graph with at least three vertices is contained, on the same vertex set, in a drawable triangulation with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
