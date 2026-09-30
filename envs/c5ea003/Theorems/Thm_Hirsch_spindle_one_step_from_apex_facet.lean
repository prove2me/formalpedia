-- Prove2me | Theorems.Thm_Hirsch_spindle_one_step_from_apex_facet
-- name    : Hirsch.spindle_one_step_from_apex_facet
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T14:49:13.805813+00:00
-- url     : https://prove2.me/theorems/7a6dc674-21f4-4903-af28-f0dcb256049a
-- title:
--   Strong $d$-step step from a chosen apex facet
-- statement:
--   Santos' inductive step, starting from a chosen facet through one apex.
--
--   Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope described by $n$ inequalities, with $0<d$ and $n>2d$. Suppose $u,v$ are extreme points forming a spindle of length greater than $d$, and inequality $i_0$ is tight at $u$.
--
--   Then there exist a nonempty bounded H-polytope $P'\subseteq\mathbb R^{d+1}$ described by $n+1$ inequalities, together with extreme points $u',v'$ of $P'$, such that $P'$ is a spindle with apices $u',v'$ and there is no padded vertex-edge walk of length $d+1$ from $u'$ to $v'$.
--
--   This is the polar of the one-point-suspension-plus-perturbation in Santos, Theorem 2.6: one first wedges over the facet through $u$ corresponding to $i_0$, then perturbs so that the image of the opposite base becomes a facet, increasing the spindle length by one.
--
--   **Formalization Note.** The facet through $u$ is passed as an index $i_0$ with $\langle a_{i_0},u\rangle=b_{i_0}$.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Theorem 1.5 and Theorem 2.6 (inductive step, Section 2.2).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

/-- Santos' inductive step, starting from a chosen facet through one apex.

If $P\subseteq\mathbb R^d$ is a $d$-spindle of length greater than $d$ with
$n>2d$ inequalities, and inequality $i_0$ is tight at the apex $u$, then
the one-point-suspension-plus-perturbation of Santos (Theorem 2.6, polarised)
produces a $(d+1)$-spindle with $n+1$ inequalities and length greater than
$d+1$. -/
theorem spindle_one_step_from_apex_facet (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (i0 : Fin n)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (htight : ⟪a i0, u⟫ = b i0)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
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
