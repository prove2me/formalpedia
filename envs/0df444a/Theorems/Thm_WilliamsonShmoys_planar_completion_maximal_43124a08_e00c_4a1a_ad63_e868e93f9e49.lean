-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_43124a08_e00c_4a1a_ad63_e868e93f9e49
-- name    : WilliamsonShmoys.planar_completion_maximal_43124a08_e00c_4a1a_ad63_e868e93f9e49
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:00:54.832409+00:00
-- url     : https://prove2.me/theorems/89637aca-ffa0-41ed-b9cf-1c76e159d267
-- title:
--   A planar graph has an edge-maximal planar completion
-- statement:
--   Any graph with a crossing-free drawing has a supergraph on the same finite vertex set that is planar and inclusion-maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_maximal_43124a08_e00c_4a1a_ad63_e868e93f9e49 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K.edgeSet ⊆ H.edgeSet ∧ (WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet) := by sorry
