-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:25.753843+00:00
-- url     : https://prove2.me/theorems/acfdd557-6461-4967-8353-28fd3dec40e2
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph. This isolates the finite maximization step from the target: the parent applies the extension hypothesis to show the maximal supergraph is connected. The child can be proved by maximizing edge count over the finite family of supergraphs of G that have planar drawings; a strict extension strictly increases edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
