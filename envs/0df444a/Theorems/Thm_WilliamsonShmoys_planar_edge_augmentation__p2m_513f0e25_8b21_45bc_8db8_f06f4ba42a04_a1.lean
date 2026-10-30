-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:31:10.887679+00:00
-- url     : https://prove2.me/theorems/de26d9eb-6d23-47e8-ab7e-7d74d86b498f
-- title:
--   A planar graph below the bound has a strict drawable extension
-- statement:
--   If a drawable graph on at least three vertices has fewer than 3n−6 edges, it has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hGap : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
