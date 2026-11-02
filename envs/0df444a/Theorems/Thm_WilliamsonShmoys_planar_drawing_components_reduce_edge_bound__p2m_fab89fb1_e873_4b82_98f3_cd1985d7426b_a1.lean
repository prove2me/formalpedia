-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- name    : WilliamsonShmoys.planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:03.144212+00:00
-- url     : https://prove2.me/theorems/e90140a3-abea-4505-a30e-e91c6b895857
-- title:
--   Reduce the planar edge bound to connected graphs
-- statement:
--   If the connected planar edge bound holds for every finite linearly ordered vertex type, then it holds for any finite graph satisfying HasPlanarDrawingOn. Decompose into connected components, restrict the drawing to each component, use the connected bound on components of size at least three, and handle components of size one or two directly; summing the component estimates gives the result for total vertex count at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        3 <= Fintype.card W → G.Connected → HasPlanarDrawingOn G →
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj
           G.edgeFinset.card + 6 <= 3 * Fintype.card W)) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
