-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:18.366896+00:00
-- url     : https://prove2.me/theorems/a06f5bd4-9714-4d93-b157-09922cf717e8
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> Eq L K)) := by sorry
