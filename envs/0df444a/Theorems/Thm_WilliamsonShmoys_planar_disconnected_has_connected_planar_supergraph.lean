-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_connected_planar_supergraph
-- name    : WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T08:00:24.405276+00:00
-- url     : https://prove2.me/theorems/7efa5617-93fa-4313-acc1-2c85daa74618
-- title:
--   Connect a disconnected planar graph by planar augmentation
-- statement:
--   Every disconnected finite graph with the specified planar drawing has a connected planar supergraph on the same vertices. This strengthens the target by requiring the extension to be connected, and it also drops the target’s lower bound on the number of vertices. A proof route is induction on the number of connected components: use the planar embedding to find components incident to a common face, add an edge through that face, and repeat. Isolated and nested components require choosing a suitable common face; the false claim that an arbitrary pair of unreachable vertices can be joined is not used.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
