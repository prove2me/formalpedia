-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2
-- name    : WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:31.752086+00:00
-- url     : https://prove2.me/theorems/6eb1d1e9-05be-4cdb-8344-dedf44e2bf5b
-- title:
--   A disconnected drawable graph with at least three vertices has a drawable strict extension
-- statement:
--   A disconnected graph on a finite linearly ordered vertex type with at least three vertices, if it has a crossing-free drawing, has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  sorry
