-- Prove2me | Theorems.Thm_WilliamsonShmoys_eulerIncidence_edge_bound__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
-- name    : WilliamsonShmoys.eulerIncidence_edge_bound__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:13.054192+00:00
-- url     : https://prove2.me/theorems/0794fa2f-6f08-4980-8d67-aa360ef1265f
-- title:
--   Euler and incidence counts imply the planar edge bound
-- statement:
--   If a finite simple graph has at least three vertices, and numbers of faces and boundary incidences satisfy Euler’s equation, at least two incidences per edge, and at least three incidences per face, then the graph has at most `3|V| - 6` edges. The parent applies this arithmetic reduction to the face and incidence counts supplied by the geometric child. The `|V| ≥ 3` condition is essential for this statement: without it, the numeric assumptions permit a counterexample at two vertices. A direct proof route is to combine `3f ≤ i` and `2|E| ≤ i`, substitute Euler’s equation, and discharge the resulting natural-number arithmetic with `omega`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.eulerIncidence_edge_bound__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (f i : ℕ)
    (hn : 3 ≤ Fintype.card V)
    (hEuler : Fintype.card V + f = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2)
    (hEdgeInc : 2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ≤ i)
    (hFaceInc : 3 * f ≤ i) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
