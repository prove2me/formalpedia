-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
-- name    : WilliamsonShmoys.planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:10.362231+00:00
-- url     : https://prove2.me/theorems/07b4009a-04ca-4342-a9d5-b274d08c0821
-- title:
--   Extend a planar graph below the maximal edge count
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3n−6 edges has a drawable strict edge supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    G.edgeFinset.card < 3 * Fintype.card V - 6 →
    ∃ H : SimpleGraph V,
      G.edgeFinset ⊆ H.edgeFinset ∧
      HasPlanarDrawingOn H ∧
      ¬ H.edgeFinset ⊆ G.edgeFinset := by
  sorry
