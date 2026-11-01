-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:08.558678+00:00
-- url     : https://prove2.me/theorems/98bb09a3-5fff-4d40-87aa-050eb50db2d4
-- title:
--   Induced subgraphs inherit a planar drawing
-- statement:
--   Restricting the vertex placement and edge arcs to a subset gives a planar drawing of the induced subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (s : Set V)
    [Fintype {x // x ∈ s}]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    WilliamsonShmoys.HasPlanarDrawingOn (M.induce s) := by sorry
