-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation__p2m_5324d67d_14ae_438c_82d4_e1293378ffbf_a1
-- name    : WilliamsonShmoys.maximal_planar_augmentation__p2m_5324d67d_14ae_438c_82d4_e1293378ffbf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:27.705204+00:00
-- url     : https://prove2.me/theorems/0e6910fa-4f99-44c6-b0a3-c431dbc27fef
-- title:
--   Extend a finite planar drawing to maximal planar edge count
-- statement:
--   Every finite graph with a drawing satisfying `HasPlanarDrawingOn` is a subgraph of a drawable graph whose number of edges is `3n - 6`, with subtraction interpreted in Nat.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_augmentation__p2m_5324d67d_14ae_438c_82d4_e1293378ffbf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        3 * Fintype.card V - 6 = L.edgeFinset.card) := by sorry
