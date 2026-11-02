-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:07.482863+00:00
-- url     : https://prove2.me/theorems/b6ef5ab1-c465-4724-83b5-1fd8c793e204
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   Every graph on at least three finite linearly ordered vertices with a drawing in the specified crossing-free sense has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (HasPlanarDrawingOn K)
        (Eq K.edgeFinset.card (3 * Fintype.card V - 6))) := by sorry
