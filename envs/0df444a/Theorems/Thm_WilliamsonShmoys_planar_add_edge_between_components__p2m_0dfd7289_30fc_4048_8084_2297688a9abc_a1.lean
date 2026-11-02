-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_components__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:02.892063+00:00
-- url     : https://prove2.me/theorems/e631757e-99f4-4ba7-8219-0049a373bba8
-- title:
--   Add a drawable edge between distinct components
-- statement:
--   Given a drawable graph and vertices in different components, adjoining the edge between them preserves drawability and gives a proper supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_components__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (u v : V) (huv : ¬ M.Reachable u v) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Adj u v ∧
      HasPlanarDrawingOn N ∧ N ≠ M := by
  sorry
