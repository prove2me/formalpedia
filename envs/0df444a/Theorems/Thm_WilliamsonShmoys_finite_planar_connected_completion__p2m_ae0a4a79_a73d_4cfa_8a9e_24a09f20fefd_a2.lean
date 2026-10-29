-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_connected_completion__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
-- name    : WilliamsonShmoys.finite_planar_connected_completion__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:36:24.211741+00:00
-- url     : https://prove2.me/theorems/00d84506-131e-4af5-b179-a5b238d43337
-- title:
--   Finite maximality yields a connected planar completion
-- statement:
--   If every disconnected planar supergraph admits an extension adding an edge between distinct unreachable vertices, then there is a connected planar supergraph. Choose a planar supergraph containing the original graph with maximal edge count. Since there are finitely many simple graphs on the finite vertex type, such a maximum exists. If it were disconnected, the cardinality hypothesis supplies distinct unreachable vertices, and the extension increases the edge count, contradicting maximality. This discharges the finite maximality and connectedness argument; the geometric extension is the remaining core.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_connected_completion__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V)
    (hExtend : ∀ (H : SimpleGraph V), G ≤ H → HasPlanarDrawingOn H →
      ∀ u v : V, u ≠ v → ¬ H.Reachable u v →
        ∃ J : SimpleGraph V, H ≤ J ∧ J.Adj u v ∧ HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, G ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
