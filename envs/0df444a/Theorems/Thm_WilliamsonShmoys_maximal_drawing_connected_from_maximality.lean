-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_connected_from_maximality
-- name    : WilliamsonShmoys.maximal_drawing_connected_from_maximality
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:21:09.100959+00:00
-- url     : https://prove2.me/theorems/3f191f74-7c0a-4182-adef-ae56688b2b94
-- title:
--   A maximal drawable graph with at least three vertices is connected
-- statement:
--   A finite graph on at least three vertices with a crossing-free drawing is connected if no drawable graph on the same vertices can strictly extend its edge set. The size condition rules out relying on small-vertex degeneracies. A proof route is to take vertices in distinct components and add an edge between components by routing an arc through the complement of the finite drawing, contradicting maximality. This removes the connectedness step from the parent; the drawing-extension argument must still be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_connected_from_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    K.Connected := by sorry
