-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_plane_euler_data_supergraph_of_drawing
-- name    : WilliamsonShmoys.exists_plane_euler_data_supergraph_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:00:32.51854+00:00
-- url     : https://prove2.me/theorems/de2f6bef-206f-4449-8fd5-c41a163d3767
-- title:
--   Connected planar supergraph with Euler face data
-- statement:
--   Every drawing in the target hypothesis, on at least three vertices, admits a connected planar supergraph on the same vertex set whose finite face data satisfies Euler’s formula and the minimum face-degree count. The route is to join distinct components by noncrossing arcs, then form the plane embedding’s faces and count edge-side incidences. The lower bound of three incidences per face uses simplicity and the at-least-three-vertices condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlaneEulerData

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_plane_euler_data_supergraph_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlaneEulerData K := by
  sorry
