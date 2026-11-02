-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:29.792733+00:00
-- url     : https://prove2.me/theorems/eddf1ef1-c9f3-44c4-b9de-b9991014893d
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   If one graph's edge set is contained in another's, any drawing satisfying the given predicate for the larger graph also satisfies it for the subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by sorry
