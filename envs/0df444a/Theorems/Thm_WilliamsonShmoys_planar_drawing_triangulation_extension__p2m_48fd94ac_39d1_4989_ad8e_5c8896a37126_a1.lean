-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_48fd94ac_39d1_4989_ad8e_5c8896a37126_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_48fd94ac_39d1_4989_ad8e_5c8896a37126_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:36:26.151732+00:00
-- url     : https://prove2.me/theorems/b18c4da7-894a-4166-8a45-3e8b256f043a
-- title:
--   Extremal planar completion on the same vertex type
-- statement:
--   Every finite drawable simple graph with at least three vertices is contained, on the same vertex type, in a drawable graph with exactly 3|V| − 6 edges. The child isolates the topological completion and triangulation step; the parent uses only its edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_48fd94ac_39d1_4989_ad8e_5c8896a37126_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : forall (K : SimpleGraph V), DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    Exists fun K : SimpleGraph V =>
      H.edgeFinset.card <= K.edgeFinset.card /\
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
