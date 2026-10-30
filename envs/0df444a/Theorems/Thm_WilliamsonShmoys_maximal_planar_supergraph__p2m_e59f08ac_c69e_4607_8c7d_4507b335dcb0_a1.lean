-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:11.557656+00:00
-- url     : https://prove2.me/theorems/dc23d7df-a1d9-410e-b730-0e5240e61428
-- title:
--   A maximal planar supergraph exists on a finite vertex type
-- statement:
--   Every planar graph on a finite linearly ordered vertex type has a planar supergraph on the same type that is maximal under graph inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V => And (LE.le H K) (And (HasPlanarDrawingOn K) (forall (L : SimpleGraph V), LE.le K L -> HasPlanarDrawingOn L -> L = K)) := by sorry
