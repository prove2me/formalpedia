-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1
-- name    : WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:56.4393+00:00
-- url     : https://prove2.me/theorems/b9851501-c1e8-4fe9-a3db-2983e821165e
-- title:
--   A disconnected finite plane graph has a drawable strict extension
-- statement:
--   Any disconnected graph on a finite linearly ordered vertex type that has a crossing-free drawing has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  sorry
