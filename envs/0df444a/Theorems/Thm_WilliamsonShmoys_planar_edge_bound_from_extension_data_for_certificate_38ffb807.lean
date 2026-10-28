-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_extension_data_for_certificate_38ffb807
-- name    : WilliamsonShmoys.planar_edge_bound_from_extension_data_for_certificate_38ffb807
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:06:23.622264+00:00
-- url     : https://prove2.me/theorems/7f797a7d-aca9-4a26-9aa9-6a0b0952b9f3
-- title:
--   Transfer the connected Euler bound through a planar extension
-- statement:
--   If a drawn graph on at least three vertices has a connected drawn supergraph on the same vertices, and every connected drawn graph on those vertices satisfies the Euler edge bound, then the original graph satisfies it too.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_from_extension_data_for_certificate_38ffb807
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hext : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconnBound : ∀ (G : SimpleGraph V), 3 ≤ Fintype.card V → G.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
