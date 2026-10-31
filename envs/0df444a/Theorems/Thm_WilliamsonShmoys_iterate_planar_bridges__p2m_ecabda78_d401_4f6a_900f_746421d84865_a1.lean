-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
-- name    : WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:47.949973+00:00
-- url     : https://prove2.me/theorems/8875bb45-86a4-4d7c-b2ea-8d56d84fd5c3
-- title:
--   Iterate drawable bridges to connect a graph
-- statement:
--   If every disconnected drawable graph on a fixed finite vertex type admits a drawable edge addition joining two different reachable components, then every disconnected drawable starting graph has a connected drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hStep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ u v : V,
        u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
        HasPlanarDrawingOn
          (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)))
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
