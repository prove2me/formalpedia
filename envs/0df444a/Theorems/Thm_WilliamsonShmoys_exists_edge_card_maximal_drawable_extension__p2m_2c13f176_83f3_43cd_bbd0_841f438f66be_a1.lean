-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- name    : WilliamsonShmoys.exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:08.490299+00:00
-- url     : https://prove2.me/theorems/eb4260ba-9d59-4700-a2ea-3c6102b49134
-- title:
--   Finite edge-count maximum among drawable extensions
-- statement:
--   Every drawable graph on this finite vertex type has a drawable supergraph containing it whose edge-set cardinality is at least that of every drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
