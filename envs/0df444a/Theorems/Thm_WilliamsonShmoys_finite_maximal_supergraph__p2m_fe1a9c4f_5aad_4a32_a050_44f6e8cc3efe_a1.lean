-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:10.741901+00:00
-- url     : https://prove2.me/theorems/0a9ffbbd-ef73-4dc2-83ce-d5d9f13e1347
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   On a finite vertex type, a graph satisfying a downward-closed property is contained in a graph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1 {V : Type} [Fintype V] (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hPK : P K) (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) : ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ ∀ J : SimpleGraph V, H ≤ J → P J → J ≤ H := by sorry
