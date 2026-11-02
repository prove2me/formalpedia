-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:19.390321+00:00
-- url     : https://prove2.me/theorems/8c45446d-c348-4a00-bfb8-7c43777f283d
-- title:
--   Planar drawings pass to subgraphs
-- statement:
--   A graph with a planar drawing on the given vertex type passes that drawing to every subgraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V} (hAB : A ≤ B)
    (hB : WilliamsonShmoys.HasPlanarDrawingOn B) :
    WilliamsonShmoys.HasPlanarDrawingOn A := by
  sorry
