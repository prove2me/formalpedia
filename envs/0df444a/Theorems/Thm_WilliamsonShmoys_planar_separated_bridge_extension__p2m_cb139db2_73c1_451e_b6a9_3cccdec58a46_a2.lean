-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2
-- name    : WilliamsonShmoys.planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:40.150578+00:00
-- url     : https://prove2.me/theorems/353b61e0-8cec-4373-8be0-6e3443fc0711
-- title:
--   Add a planar edge between distinct original components
-- statement:
--   For a finite drawable graph on at least three vertices that is disconnected, there is a planar supergraph with a new edge whose endpoints were in different connected components of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Adj u v ∧ ∃ G : SimpleGraph V,
      H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v ∧
        ¬ Relation.ReflTransGen H.Adj u v := by sorry
