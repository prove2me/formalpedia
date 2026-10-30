-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- name    : WilliamsonShmoys.exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:22.27899+00:00
-- url     : https://prove2.me/theorems/53c17418-11ef-424f-a50a-b8723b415e73
-- title:
--   Extract a planar triangulation counting certificate
-- statement:
--   A finite crossing-free drawing of a simple graph on at least three vertices yields a same-vertex simple supergraph with finite face data satisfying Euler’s relation, face-degree lower bounds, and the face-edge incidence count. This isolates the topological extension and face-boundary extraction from the edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : Nonempty (WilliamsonShmoys.PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 H) := by sorry
