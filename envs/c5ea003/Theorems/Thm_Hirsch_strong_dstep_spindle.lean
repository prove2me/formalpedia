-- Prove2me | Theorems.Thm_Hirsch_strong_dstep_spindle
-- name    : Hirsch.strong_dstep_spindle
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T13:24:50.400558+00:00
-- url     : https://prove2.me/theorems/51a39fac-8270-4e34-a7a0-4edf053137e7
-- title:
--   Strong $d$-step theorem for spindles
-- statement:
--   (Santos, strong $d$-step theorem for spindles.) Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope described by $n$ inequalities, with $0<d\le n$. Suppose $u,v$ are extreme points of $P$ such that every describing inequality is tight at exactly one of $u$ or $v$ (a spindle with apices $u,v$), and there is no padded vertex-edge walk of length $d$ from $u$ to $v$ (the spindle has length at least $d+1$).
--
--   Then there exist a dimension $D=n-d$ and a nonempty bounded H-polytope $P'\subseteq\mathbb R^D$ described by exactly $2D$ inequalities such that
--
--   $$
--   \lnot\mathrm{DiamLE}(P',D).
--   $$
--
--   In particular $P'$ has $2D$ facets in dimension $D$, so the Hirsch bound is $D$, and $P'$ is a counterexample to the $d$-step conjecture, hence also to the Hirsch conjecture.
--
--   The construction is Santos's one-point suspension / strong $d$-step map: from a $d$-spindle with $n$ facets and length $\ell>d$ one obtains an $(n-d)$-spindle with $2n-2d$ facets and length at least $\ell+n-2d$. Here $\ell\ge d+1$ yields length at least $n-d+1$, so the diameter exceeds $D=n-d$.
--
--   **Formalization Note** The output description has type `Fin (2*D) → EuclideanSpace ℝ (Fin D)` with `D = n-d` (truncated subtraction, legal by $d\le n$). The input length hypothesis is the nonexistence of a padded walk of length $d$, matching `DiamLE` style.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Annals of Mathematics 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Theorem 1.5 (Strong d-step Theorem for spindles), pp. 387-388 (arXiv v3); polar/prismatoid form: B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015), arXiv:1202.4701, Theorem 1.1.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem strong_dstep_spindle (d n : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (D : ℕ) (a' : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b' : Fin (2 * D) → ℝ),
      D = n - d ∧
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      ¬ DiamLE (Hpoly a' b') D := by sorry

end Hirsch
