-- Prove2me | Theorems.Thm_WilliamsonShmoys_supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- name    : WilliamsonShmoys.supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:37.420217+00:00
-- url     : https://prove2.me/theorems/858813b9-065b-47ac-a74a-0db29a26787b
-- title:
--   Iterate strict edge extensions to a connected supergraph
-- statement:
--   For a finite vertex type, any graph property preserved by a step that adds a previously absent edge to each disconnected graph can be extended to a connected supergraph with that property. A proof route is induction on the finite number of unordered vertex pairs that are not edges: each step strictly decreases this number while preserving all existing edges and the property. This separates finite component bookkeeping from the planar geometry. Applying it with P := HasPlanarDrawingOn and the preceding one-edge lemma gives the target. The boundary case is a graph already connected; the induction must also account for vertex types with fewer than two vertices, where no disconnected graph can require an extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G)
    (hstep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ H : SimpleGraph V,
        (∀ u v, K.Adj u v → H.Adj u v) ∧
        (∃ u v, ¬ K.Adj u v ∧ H.Adj u v) ∧ P H) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧ H.Connected ∧ P H := by sorry
