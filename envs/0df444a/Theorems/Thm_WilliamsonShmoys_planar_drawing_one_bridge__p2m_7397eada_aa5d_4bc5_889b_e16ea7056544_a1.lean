-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_bridge__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
-- name    : WilliamsonShmoys.planar_drawing_one_bridge__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:13.621177+00:00
-- url     : https://prove2.me/theorems/066ddc4d-10c5-40b4-b420-ae6753980591
-- title:
--   Add a planar edge between components
-- statement:
--   For a finite graph with a crossing-free drawing that is disconnected, add at least one edge between distinct components while retaining a crossing-free drawing on the same vertex set. The strict edge-count increase ensures progress for the iteration lemma. A proof route is to choose vertices in different components, use a path in the plane complement of the finite embedded graph to route an arc between them, and extend the drawing witness with that arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_one_bridge__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hdis : ¬ H.Connected) : ∃ K : SimpleGraph V, H ≤ K ∧ H.edgeSet.ncard < K.edgeSet.ncard ∧ HasPlanarDrawingOn K := by sorry
