-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_edge_bound
-- name    : WilliamsonShmoys.planar_triangulation_certificate_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:09:07.692623+00:00
-- url     : https://prove2.me/theorems/392b43c1-80b0-4f69-9d89-bd1cd04ce37f
-- title:
--   Edge bound from triangulation counts
-- statement:
--   A graph contained in an extension whose finite edge and face counts satisfy Euler's equation and the triangular-incidence equation has at most three times its vertex count minus six edges, expressed without natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_certificate_edge_bound
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (c : PlanarTriangulationCertificate G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
