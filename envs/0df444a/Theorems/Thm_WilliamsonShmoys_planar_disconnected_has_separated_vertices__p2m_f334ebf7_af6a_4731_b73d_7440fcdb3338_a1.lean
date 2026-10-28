-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
-- name    : WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:16.011406+00:00
-- url     : https://prove2.me/theorems/8e171d0a-651d-45cf-84b1-d01abdfb969d
-- title:
--   Disconnectedness yields separated nonadjacent vertices
-- statement:
--   A disconnected simple graph on at least two vertices has distinct vertices in different connected components, and they are not adjacent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

end WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 2 ≤ Fintype.card V)
    (hNot : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧ ¬ K.Reachable u v := by sorry
