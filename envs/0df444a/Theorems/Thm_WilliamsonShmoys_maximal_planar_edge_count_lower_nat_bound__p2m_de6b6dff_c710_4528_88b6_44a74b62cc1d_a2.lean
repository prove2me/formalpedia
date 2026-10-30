-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:55:39.363522+00:00
-- url     : https://prove2.me/theorems/c55b2f93-facd-49c1-bd67-d73f047e3dad
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   A connected drawable graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V|−6 edges. Maximality should force a triangulation: if a face has more than three boundary vertices, add a drawable diagonal, contradicting maximality; Euler counting then gives the bound. This separates the maximality argument from the general planar upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
