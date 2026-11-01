-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:45.618146+00:00
-- url     : https://prove2.me/theorems/31f8bce1-63f0-4276-adb7-4172c398524b
-- title:
--   Planar drawings restrict to edge-subgraphs
-- statement:
--   If a graph’s edge set is contained in another graph’s edge set, a crossing-free drawing of the larger graph restricts to a crossing-free drawing of the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (A B : SimpleGraph V) (dA : DecidableRel A.Adj) (dB : DecidableRel B.Adj)
    (hAB : (letI : DecidableRel A.Adj := dA
            letI : DecidableRel B.Adj := dB
            A.edgeFinset ⊆ B.edgeFinset))
    (hB : HasPlanarDrawingOn B) : HasPlanarDrawingOn A := by sorry
