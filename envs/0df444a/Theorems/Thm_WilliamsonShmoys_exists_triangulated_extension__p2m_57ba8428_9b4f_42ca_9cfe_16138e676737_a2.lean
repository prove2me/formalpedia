-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2
-- name    : WilliamsonShmoys.exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:20:20.224482+00:00
-- url     : https://prove2.me/theorems/fd2f6266-9b0d-43ab-8372-1dbf529a8a08
-- title:
--   Every finite drawable graph extends to an edge-maximal planar graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
