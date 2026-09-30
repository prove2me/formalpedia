-- Prove2me | Theorems.Thm_Hirsch_spindle_one_step
-- name    : Hirsch.spindle_one_step
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T14:20:57.298299+00:00
-- url     : https://prove2.me/theorems/dae7c11a-f27f-4e77-96cd-8dd1b3ef0d21
-- title:
--   One-step strong $d$-step construction for spindles
-- statement:
--   This is the inductive step of Santos' strong $d$-step theorem for spindles (the polar form of the prismatoid construction in Section 2.2).
--
--   Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope described by $n$ inequalities, with $0<d$ and $n>2d$. Suppose $u,v$ are extreme points of $P$ such that every describing inequality is tight at exactly one of $u$ or $v$ (a spindle with apices $u,v$), and there is no padded vertex-edge walk of length $d$ from $u$ to $v$.
--
--   Then there exist a nonempty bounded H-polytope $P'\subseteq\mathbb R^{d+1}$ described by $n+1$ inequalities, together with extreme points $u',v'$ of $P'$, such that $P'$ is again a spindle with apices $u',v'$, and there is no padded vertex-edge walk of length $d+1$ from $u'$ to $v'$.
--
--   Iterating this step $n-2d$ times produces a spindle of dimension $n-d$ with $2n-2d$ facets and length greater than $n-d$, which is the content of the strong $d$-step theorem.
--
--   **Formalization Note.** Length is encoded by the non-existence of a padded walk of length equal to the ambient dimension, matching `Hirsch.strong_dstep_spindle`. The construction is the polar of the one-point-suspension-plus-perturbation of a prismatoid in Santos, Theorem 2.6.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Annals of Mathematics 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Theorem 1.5 and Theorem 2.6 (inductive step, Section 2.2), polar/prismatoid form.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem spindle_one_step (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
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
