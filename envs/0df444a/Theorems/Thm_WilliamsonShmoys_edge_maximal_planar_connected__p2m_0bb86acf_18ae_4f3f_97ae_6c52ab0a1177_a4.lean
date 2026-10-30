-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_connected__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
-- name    : WilliamsonShmoys.edge_maximal_planar_connected__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:18.957525+00:00
-- url     : https://prove2.me/theorems/dbcaa6ab-2cb7-484f-92db-ffa98663625a
-- title:
--   Edge-maximal planar graphs are connected
-- statement:
--   A planar graph on a finite linearly ordered vertex type with at least three vertices is connected if it has no proper planar edge supergraph on that same type. If it were disconnected, drawings of distinct components could be placed in disjoint regions and joined by an edge while retaining all edges; that planar supergraph would contradict hMax. This child isolates the topological connectivity argument from the finite maximal-extension argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_connected__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) : H.Connected := by sorry
