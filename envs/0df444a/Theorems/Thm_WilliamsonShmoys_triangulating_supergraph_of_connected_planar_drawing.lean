-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulating_supergraph_of_connected_planar_drawing
-- name    : WilliamsonShmoys.triangulating_supergraph_of_connected_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:58:09.319994+00:00
-- url     : https://prove2.me/theorems/257d87e0-269e-43a7-ab5e-fbfbfecb9985
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   There is an inclusion-maximal planar supergraph of the connected input graph on the same finite vertex type. This child removes the existence and maximality construction from the parent. Prove it by choosing a planar supergraph with maximum edge count from the finite nonempty family of supergraphs of J; adding edges preserves connectedness, and the planar drawing is part of the candidate family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulating_supergraph_of_connected_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by
  sorry
