-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
-- name    : WilliamsonShmoys.edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:19.065187+00:00
-- url     : https://prove2.me/theorems/63ad9a14-da0c-4363-acd0-29ef03d610e6
-- title:
--   Strict planar edge augmentation below the maximal bound
-- statement:
--   For a drawable simple graph on at least three vertices, if its edge count is strictly below 3|V|−6, there is a drawable graph on the same vertex set whose edges include the original edges and strictly extend them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hsmall : L.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      L.edgeFinset ≠ M.edgeFinset := by
  sorry
