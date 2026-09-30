-- Prove2me | Theorems.Thm_Hirsch_spindle_one_step_axis
-- name    : Hirsch.spindle_one_step_axis
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T15:01:24.733751+00:00
-- url     : https://prove2.me/theorems/3e8cb35f-92d6-422d-bd70-a7fece9a39f4
-- title:
--   Strong $d$-step step with apices $\pm e_d$
-- statement:
--   Santos' inductive step in standard position, with apices $\pm e_d$.
--
--   Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope described by $n>2d$ inequalities, with $d>0$, whose apices are $e_d$ and $-e_d$, forming a spindle of length greater than $d$, and suppose inequality $i_0$ is tight at $e_d$.
--
--   Then there is a nonempty bounded H-polytope $P'\subseteq\mathbb R^{d+1}$ described by $n+1$ inequalities which is a spindle of length greater than $d+1$.
--
--   This is Theorem 2.6 of Santos written after the apices have been moved to $\pm e_d$: one-point-suspension of the polar prismatoid over the vertex dual to $i_0$, followed by the perturbation that makes the opposite base a facet.
--
--   **Formalization Note.** Apices are `EuclideanSpace.single ⟨d-1, _⟩ (±1)`.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Theorem 2.6 (inductive step in Section 2.2).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

/-- Santos' inductive step in standard position: apices $\pm e_d$, facet through
the positive apex.

If $P\subseteq\mathbb R^d$ is a $d$-spindle of length greater than $d$ with
apices $e_d$ and $-e_d$, $n>2d$ inequalities, and inequality $i_0$ tight at
$e_d$, then there is a $(d+1)$-spindle with $n+1$ inequalities and length
greater than $d+1$. -/
theorem spindle_one_step_axis (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hv : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i,
      (⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i) ↔
        ⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b i)
    (htight : ⟪a i0, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i0)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
          w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
        ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
            ∀ j < d + 1, w j = w (j + 1) ∨
              Adj (Hpoly a' b') (w j) (w (j + 1))) := by sorry

end Hirsch
