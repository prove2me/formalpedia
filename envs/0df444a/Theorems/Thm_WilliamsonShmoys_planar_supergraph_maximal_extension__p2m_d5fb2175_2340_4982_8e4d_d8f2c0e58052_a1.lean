-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- name    : WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:58.841556+00:00
-- url     : https://prove2.me/theorems/9a3aed6d-2bec-4e6f-a443-353e67f8b6ae
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every connected graph in the target’s hypotheses has a planar supergraph on the same vertex set that is inclusion-maximal among planar supergraphs. The connectedness and size assumptions are retained from the parent; the finite-maximization argument itself only needs the drawing and finiteness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
