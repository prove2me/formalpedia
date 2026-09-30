-- Prove2me | Theorems.Thm_Hirsch_balanced_hpoly_transfer
-- name    : Hirsch.balanced_hpoly_transfer
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T04:27:03.732432+00:00
-- url     : https://prove2.me/theorems/e7efc9ee-dec1-4a30-bc66-5a19ad645c7f
-- title:
--   Balancing H-polytopes with a diameter-transfer map
-- statement:
--   Let $P\subseteq\mathbb{R}^d$ be a nonempty bounded H-polytope cut out by $n$ linear inequalities $\langle a_i,x\rangle\le b_i$. There exist an ambient dimension
--
--   $$
--   D=d+(n-2d)
--   $$
--
--   (with natural-number subtraction) and a nonempty bounded H-polytope $Q\subseteq\mathbb{R}^D$ described by exactly $2D$ inequalities, such that for every $L\in\mathbb{N}$,
--
--   $$
--   \operatorname{DiamLE}(Q,L)\Longrightarrow\operatorname{DiamLE}(P,L).
--   $$
--
--   In particular $D\le n+d$, and $D=\max(d,n-d)$. When $n\le 2d$ the construction pads tautological inequalities $0\cdot x\le 1$; when $n>2d$ it iterates a description-level Klee–Walkup wedge, replacing one inequality $a_1\cdot x\le b_1$ by $a_1\cdot x+t\le b_1$ and $-t\le 0$. Projection of the wedge sends vertices to vertices and edges to edges or points, so padded walks of a given length descend. The argument uses the given inequality description: redundant inequalities, lower-dimensional polytopes, and the zero-dimensional case are included.
--
--   This is formalization infrastructure for the classical wedge/$d$-step reduction, not a new diameter bound. Combined with a polynomial bound on the balanced subfamily $n=2D$, it yields the unrestricted polynomial Hirsch conjecture with the same exponent.
--
--   **Formalization Note** The witnesses $a_Q,b_Q$ are an explicit H-description in `EuclideanSpace ℝ (Fin D)`. Boundedness is `Bornology.IsBounded`. The identity $D=d+(n-2d)$ uses Lean's truncated subtraction.
-- source:
--   F. Santos, Recent progress on the combinatorial diameter of polytopes and simplicial complexes, TOP 21 (2013), arXiv:1307.5900, Section 4.2, Lemma 5 (classical wedge / d-step lemma of Klee--Walkup); Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967) 53-78. Description-level adaptation for the Prove2Me Hirsch model, in which n counts all describing inequalities and DiamLE is a padded walk.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem balanced_hpoly_transfer (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
      D = d + (n - 2 * d) ∧
      (Hpoly aQ bQ).Nonempty ∧
      Bornology.IsBounded (Hpoly aQ bQ) ∧
      ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L := by sorry

end Hirsch
