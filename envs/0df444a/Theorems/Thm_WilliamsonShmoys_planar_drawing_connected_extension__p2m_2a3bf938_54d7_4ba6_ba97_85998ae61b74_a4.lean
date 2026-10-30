-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:24:05.490982+00:00
-- url     : https://prove2.me/theorems/be399568-1251-49d3-ad3f-1a63dc2b7c41
-- title:
--   Connected extension of a finite planar drawing
-- statement:
--   Any finite graph with the given crossing-free drawing and at least three vertices can be extended, on the same vertex set, to a connected graph with a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ L ≤ K ∧ K.Connected := by sorry
