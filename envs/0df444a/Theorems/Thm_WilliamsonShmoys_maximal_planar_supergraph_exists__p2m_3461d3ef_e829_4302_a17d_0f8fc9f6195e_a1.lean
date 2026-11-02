-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:57.610754+00:00
-- url     : https://prove2.me/theorems/233ed0bd-e0d7-41b1-8c05-73fad0336759
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    exists J : SimpleGraph V,
      And (HasPlanarDrawingOn J)
        (And (H <= J)
          (forall K : SimpleGraph V,
            HasPlanarDrawingOn K -> J <= K -> K <= J)) := by sorry
