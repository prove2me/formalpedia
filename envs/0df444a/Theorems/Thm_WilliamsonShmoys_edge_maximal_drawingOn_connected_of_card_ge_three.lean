-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawingOn_connected_of_card_ge_three
-- name    : WilliamsonShmoys.edge_maximal_drawingOn_connected_of_card_ge_three
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:36:32.292951+00:00
-- url     : https://prove2.me/theorems/d711bd65-6efb-4e74-97dd-6cc5049e08d9
-- title:
--   An edge-maximal planar drawing on at least three vertices is connected
-- statement:
--   A planar graph on at least three vertices that is maximal under planar edge extension on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawingOn_connected_of_card_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.Connected := by
  sorry
