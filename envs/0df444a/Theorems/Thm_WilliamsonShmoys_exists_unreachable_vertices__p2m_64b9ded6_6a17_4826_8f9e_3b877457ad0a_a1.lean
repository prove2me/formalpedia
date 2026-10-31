-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
-- name    : WilliamsonShmoys.exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T06:00:39.618268+00:00
-- url     : https://prove2.me/theorems/066a7e68-cdb4-4459-8037-498e42b5a819
-- title:
--   A disconnected graph has distinct unreachable vertices
-- statement:
--   If a finite simple graph is not connected, it has distinct vertices with no path between them. The statement also handles empty or singleton vertex types: under the usual vacuous connectivity convention, nonconnectedness cannot hold for those cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hconn : ¬ Y.Connected) : ∃ u v : V, u ≠ v ∧ ¬ Y.Reachable u v := by sorry
