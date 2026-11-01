-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- name    : WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:50.603383+00:00
-- url     : https://prove2.me/theorems/82397ff1-9472-4161-8afc-6cddbeeccbb0
-- title:
--   Planar drawing is preserved under taking subgraphs
-- statement:
--   A drawing of a graph also draws each of its subgraphs on the same vertex type, by reusing its vertex positions and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
