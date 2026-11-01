-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- name    : WilliamsonShmoys.planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:10.611305+00:00
-- url     : https://prove2.me/theorems/90c5b47c-0cf7-4850-9c30-e299d649e0d1
-- title:
--   Derive the edge bound from facial walk data
-- statement:
--   For any finite family of directed edge walks satisfying the length, incidence, and Euler conditions, the graph has at most 3n − 6 edges. Summing walk lengths gives at least 3k incidences. The count condition makes the same total equal to 2m, since each undirected edge has two directed orientations. Combining 3k ≤ 2m with n + k = m + 2 yields m + 6 ≤ 3n, and hcard converts this to the stated natural-number subtraction bound. This is an independent finite-counting and arithmetic proof route; it removes the numerical edge-count argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (k : ℕ) (faces : Fin k → List (V × V))
    (hlen : ∀ i, 3 <= (faces i).length)
    (hcount : (letI : DecidableRel G.Adj := dG; ∀ u v,
      (List.flatten (List.ofFn faces)).count (u, v) =
        if G.Adj u v then 1 else 0))
    (heuler : Fintype.card V + k =
      (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) <= 3 * Fintype.card V - 6 := by sorry
