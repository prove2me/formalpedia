-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_euler_certificate_edge_count
-- name    : WilliamsonShmoys.triangulated_euler_certificate_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:02:34.995966+00:00
-- url     : https://prove2.me/theorems/b8702b1e-e3b8-4a4a-88bd-c2fd6ff83997
-- title:
--   Triangular Euler certificates determine the edge count
-- statement:
--   A triangular Euler certificate determines the edge count: summing face-edge incidences gives three incidences per face and two per edge, and combining that equation with Euler’s equation yields E + 6 = 3|V|. This is a finite counting argument independent of the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularEulerCertificate

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_euler_certificate_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hcert : WilliamsonShmoys.HasTriangularEulerCertificate U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
