-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
-- name    : WilliamsonShmoys.planar_drawing_component__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:06:52.290075+00:00
-- url     : https://prove2.me/theorems/453b80ea-9a47-4075-b2d5-0d21a793f272
-- title:
--   Restrict a planar drawing to a connected component
-- statement:
--   Each connected component’s induced graph inherits the original crossing-free drawing and is connected. The explicit `Fintype c.supp` binder addresses the runner’s reported instance synthesis failure; the parent constructs it by embedding the subtype into the finite ambient vertex type. Restrict the point and arc maps to the component support; the drawing conditions persist, and connectivity follows from paths within the component. This removes the drawing restriction and connectivity facts from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_component__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (c : G.ConnectedComponent)
    [Fintype c.supp] :
    HasPlanarDrawingOn (G.induce c.supp) ∧ (G.induce c.supp).Connected := by
  sorry
