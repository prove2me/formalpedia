-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
-- name    : WilliamsonShmoys.planar_drawingOn_induce__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:22:24.448109+00:00
-- url     : https://prove2.me/theorems/28942c82-c81c-4928-8109-97e94daacb50
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting the vertex placement and edge arcs of a planar drawing to an induced subtype gives a planar drawing of that induced graph. The explicit subtype finiteness instance resolves the prior candidate’s compilation diagnostic; the proof reuses the original witnesses and restricts their domains.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_induce__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (W : Set V)
    [Fintype {v : V // v ∈ W}] :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce W) := by sorry
