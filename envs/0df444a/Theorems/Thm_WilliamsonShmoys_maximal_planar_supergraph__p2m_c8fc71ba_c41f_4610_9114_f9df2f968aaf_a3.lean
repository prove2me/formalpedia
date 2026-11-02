-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:05.400027+00:00
-- url     : https://prove2.me/theorems/7d28393b-3717-42d0-a7e1-00f1426861ad
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under adding edges. The proof route is to maximize edge count in the finite family of drawable supergraphs; the child isolates this finite extremal step from the planar edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      HasPlanarDrawingOn P ∧
      (∀ Q : SimpleGraph V,
        (∀ u v, P.Adj u v → Q.Adj u v) →
        HasPlanarDrawingOn Q →
        (∀ u v, Q.Adj u v → P.Adj u v)) := by sorry
