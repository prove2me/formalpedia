-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bounds
-- name    : WilliamsonShmoys.sum_component_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:54:19.091177+00:00
-- url     : https://prove2.me/theorems/a2b7c832-69c1-428c-bf4b-3ce55d6aa112
-- title:
--   Aggregate local component edge bounds
-- statement:
--   For nonempty pieces whose sizes sum to at least three, local bounds of zero edges for size one, at most one edge for size two, and at most three times the size minus six for larger pieces aggregate to the same global bound. The singleton-family case uses the large-piece bound; with at least two pieces, the weaker bound of three times each size minus three suffices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (comps : Finset (Set V))
    (hne : ∀ C ∈ comps, C.Nonempty)
    (hV : 3 ≤ Fintype.card V)
    (hcard : ∑ C ∈ comps, C.ncard = Fintype.card V)
    (hlocal : ∀ C ∈ comps,
      (K.induce C).edgeSet.ncard ≤
        (if C.ncard < 3 then C.ncard - 1 else 3 * C.ncard - 6)) :
    (∑ C ∈ comps, (K.induce C).edgeSet.ncard) ≤
      3 * Fintype.card V - 6 := by sorry
