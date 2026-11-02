-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:11.033251+00:00
-- url     : https://prove2.me/theorems/6802ab23-a3ac-43c6-8aa9-163dea1542b1
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   Every simply drawn planar graph on a finite linearly ordered vertex type is contained in a planar supergraph on that same vertex type which is maximal under inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ HasPlanarDrawingOn H /\
        (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) := by sorry
