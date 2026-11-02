-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- name    : WilliamsonShmoys.maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:22.170372+00:00
-- url     : https://prove2.me/theorems/64f74f02-b5bc-4e6a-8fc6-c15e1e011319
-- title:
--   Maximal drawable graph is connected
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N -> HasPlanarDrawingOn N -> N = M) : M.Connected := by sorry
