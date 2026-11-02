-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:23.272195+00:00
-- url     : https://prove2.me/theorems/689940da-6233-467d-b487-080b0de38a3b
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges. This is the planar topology step used to derive the face count; it does not assert the target’s face-count equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v : V}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q ->
      (forall {u v : V}, Q.Adj u v -> P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    3 * Fintype.card V = P.edgeFinset.card + 6 := by sorry
