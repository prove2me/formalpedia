-- Prove2me | Theorems.Thm_Hirsch_target_face_access_of_parallel_neutral_normals
-- name    : Hirsch.target_face_access_of_parallel_neutral_normals
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T17:36:03.57045+00:00
-- url     : https://prove2.me/theorems/b00a957b-6355-4fce-8083-b53825b2270d
-- title:
--   Two-edge target-face access with parallel neutral normals
-- statement:
--   Let $P=\{p\in\mathbb R^d:\langle a_i,p\rangle\le b_i,\ i=1,\ldots,n\}$ be bounded, and let $u\ne v$ be vertices such that no nonzero row is tight at both. Suppose that all nonzero normals of rows tight at neither endpoint are real scalar multiples of one vector $c$; $c=0$ and scalars of either sign are allowed. Then a vertex on some nonzero supporting row tight at $v$ is reachable from $u$ in at most two edge steps. Stationary padding is allowed. The face is chosen existentially: it is not a prescribed face, and the endpoint need not be $v$. No simplicity or irredundancy is assumed. The bound two is sharp for this class, as witnessed by the hexagon defined by $|y|\le x$, $x+|y|\le3$, and $|y|\le1$, with endpoints $(0,0)$ and $(3,0)$.
-- source:
--   Original branch contribution, 2026-09-06: PROOF.md, Theorem and local geometric lemma in the accompanying rank-one-neutral proof package. No claim of literature priority.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.target_face_access_of_parallel_neutral_normals
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v c : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hparallel : ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i →
      ⟪a i, v⟫ ≠ b i → ∃ s : ℝ, a i = s • c) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w 2 = z ∧
        ∀ j < 2, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry
