-- Prove2me | Theorems.Thm_BookSixth_sampling_averaging_bound
-- name    : BookSixth.sampling_averaging_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:47:16.917017+00:00
-- url     : https://prove2.me/theorems/9bc4ad74-1317-406e-ad46-03a9a2ddba8e
-- title:
--   Weighted averaging under an induced selected-edge bound
-- statement:
--   This isolates the finite averaging step of the crossing lemma. Let $D$ be a good plane drawing with $N$ vertices, $M$ edges, and $C$ recorded interior crossings. Suppose every Boolean vertex selection $x$ satisfies the induced planar estimate
--
--   $$E(x) \le 3V(x)+C(x),$$
--
--   where $E(x)$ counts edges whose two endpoints are selected, $V(x)$ counts selected vertices, and $C(x)$ counts recorded crossings whose four distinct endpoints are selected. Then for every real $p$ with $0 \le p \le 1$,
--
--   $$p^2 M \le 3pN+p^4C.$$
--
--   The conditional statement deliberately does not assume or prove the topological planar edge bound. It uses only independent retention of vertices, the two distinct endpoints of an edge, and the four distinct endpoints of a recorded crossing. The geometric premise remains a separate obligation for the parent sampling bound.
--
--   **Formalization Note** The hypothesis names the induced planar estimate explicitly as `hgeom`. The proof may reuse the platform theorem `BookSixth.vertex_subset_sampling_identity` for exact finite survival weights.
-- source:
--   Derived intermediate for BookSixth.drawing_sampling_bound (6968bb2a-7af8-400f-bc59-39aa35d6ea0d), itself intermediate for Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. This statement separates finite averaging from the geometric planar edge estimate and does not quote a separately numbered result.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_vertex_subset_sampling_identity
open scoped BigOperators
open BookSixth

theorem BookSixth.sampling_averaging_bound {N M : ℕ} (D : PlaneDrawing N M)
    (hgeom : ∀ x : Fin N → Bool,
      (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true
        then (1 : ℝ) else 0) ≤
      3 * (∑ v : Fin N, if x v = true then (1 : ℝ) else 0) +
      ∑ c ∈ D.crossings,
        if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
          x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true
        then (1 : ℝ) else 0)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p^2 * (M : ℝ) ≤ 3*p*(N : ℝ) + p^4*(D.crossings.card : ℝ) := by sorry
