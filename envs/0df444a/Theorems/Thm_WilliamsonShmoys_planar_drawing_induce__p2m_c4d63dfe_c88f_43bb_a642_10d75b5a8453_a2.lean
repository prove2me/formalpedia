-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:27.112111+00:00
-- url     : https://prove2.me/theorems/de244035-c768-4837-b443-35b71fd0f5e5
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting a planar drawing to an induced vertex subset gives a drawing satisfying the same conditions for the induced subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (S : Finset V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce (↑S : Set V)) := by sorry
