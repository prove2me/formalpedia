-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:26.308983+00:00
-- url     : https://prove2.me/theorems/c50204fa-335d-4575-bac2-23cf83d1b5e4
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph that has no strict drawable supergraph on that same vertex type. The finite-choice proof route is to maximize the edge count among drawable supergraphs containing the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le N K)
        (And (HasPlanarDrawingOn K)
          (forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> L = K))) := by sorry
