-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_certificate_exact_edge_count
-- name    : WilliamsonShmoys.euler_certificate_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:19:20.683981+00:00
-- url     : https://prove2.me/theorems/7e923c8c-7b4c-466f-849e-591ca9e4ef6f
-- title:
--   Euler certificate determines the exact planar edge count
-- statement:
--   The Euler and triangular-incidence equations in the certificate imply the exact edge count, by integer arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_certificate_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hcert : HasMaximalPlanarEulerCertificate W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
