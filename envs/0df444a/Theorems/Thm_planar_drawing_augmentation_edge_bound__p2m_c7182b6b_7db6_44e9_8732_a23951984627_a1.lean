-- Prove2me | Theorems.Thm_planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1
-- name    : planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:25.889345+00:00
-- url     : https://prove2.me/theorems/6bcbc754-6431-43a3-bb11-f771114284ff
-- title:
--   Augment a planar drawing to the triangulation edge bound
-- statement:
--   For a drawable finite simple graph with at least three vertices, there is a drawable supergraph on the same vertex type with at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : LE.le 3 (Fintype.card V)) : Exists fun L : SimpleGraph V => And (LE.le K L) (And (HasPlanarDrawingOn L) (LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6))) := by sorry
