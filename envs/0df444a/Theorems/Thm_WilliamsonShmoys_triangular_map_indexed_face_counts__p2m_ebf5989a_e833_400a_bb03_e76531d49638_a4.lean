-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- name    : WilliamsonShmoys.triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:04:39.817854+00:00
-- url     : https://prove2.me/theorems/1cde335c-dfb2-4c32-a530-2aefe56335ea
-- title:
--   Derive indexed face counts from the dart equivalence
-- statement:
--   From an equivalence between indexed face corners and the darts of `H`, with every face length three, derive the total-corner count and the Euler-style equality using `hcount`. This isolates the counting work from the map-field transport. A proof route counts the sigma type as the sum of the face lengths, uses the equivalence to identify that count with the dart count, and proves that a simple graph has two darts per edge. Substituting the resulting `3 * m = 2 * H.edgeSet.ncard` into `hcount` gives both conclusions by natural-number arithmetic. The remaining core obligation is formalizing the finite-cardinality identities and arithmetic in Lean.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (m : Nat) (length : Fin m → Nat)
    (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart)
    (hlength : ∀ f, length f = 3) :
    m + Fintype.card V = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard := by sorry
