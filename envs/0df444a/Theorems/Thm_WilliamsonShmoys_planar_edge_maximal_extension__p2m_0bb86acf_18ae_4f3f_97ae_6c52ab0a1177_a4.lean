-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
-- name    : WilliamsonShmoys.planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:14.794446+00:00
-- url     : https://prove2.me/theorems/eee92ea8-a9fd-4413-9f08-bca46175a7a4
-- title:
--   Edge-maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that contains all its edges and is maximal among planar supergraphs under edge inclusion. This child removes the finite maximization and extension construction from the parent. Its hypotheses include the parent’s vertex bound; the argument can maximize among the finite family of simple graphs containing L that admit a planar drawing, a nonempty family because it contains L. The proof must formalize finiteness and maximality of that family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by sorry
