-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- name    : WilliamsonShmoys.planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:51.735079+00:00
-- url     : https://prove2.me/theorems/185c51a2-1554-4134-afb7-02a813f4e97e
-- title:
--   Restrict a planar drawing to a finite vertex subset
-- statement:
--   Restricting a crossing-free drawing to the subtype of a finite vertex subset gives a crossing-free drawing of the induced subgraph. This removes the geometric restriction step from the parent; the proof reuses the original point map and edge arcs. The `Finset` parameter ensures the subtype has the finite structure required by the drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (W : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (M.induce (W : Set V)) := by sorry
