-- Prove2me | Theorems.Thm_VectorSpaceOpt_hahn_banach_sublinear
-- name    : VectorSpaceOpt.hahn_banach_sublinear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:49:03.635513+00:00
-- url     : https://prove2.me/theorems/a074b360-85d3-41f1-a43a-3c31b19d3462
-- title:
--   Hahn–Banach theorem, extension form (sublinear version)
-- statement:
--   A real-valued functional $p$ on a vector space is **sublinear** when it is subadditive and positively homogeneous:
--
--   $$p(x + y) \le p(x) + p(y), \qquad p(\alpha x) = \alpha\, p(x) \ \text{ for } \alpha > 0.$$
--
--   Let $X$ be a real normed linear space and $p$ a **continuous** sublinear functional on $X$. Let $f$ be a linear functional defined on a subspace $M$ of $X$ and dominated there by $p$:
--
--   $$f(m) \le p(m) \qquad \text{for all } m \in M.$$
--
--   Then $f$ extends to all of $X$ under the same domination: there is a linear functional $F$ on $X$ with $F = f$ on $M$ and
--
--   $$F(x) \le p(x) \qquad \text{for all } x \in X.$$
--
--   Since $F$ is dominated by the continuous $p$, it is itself continuous.
--
--   This is the most important theorem in the book's treatment of optimization. The proof extends $f$ one dimension at a time: on $[M + y]$ the extension is determined by the single value $g(y)$, and sublinearity forces $\sup_{m}[f(m) - p(m-y)] \le \inf_{m}[p(m+y) - f(m)]$, so any $c$ between the two bounds works. Iterating over a countable dense set and passing to the limit gives $F$ on all of $X$ (in general, Zorn's lemma replaces the iteration).
--
--   Stating the domination through a sublinear $p$ rather than a norm is what makes the geometric form of the theorem — separation of convex sets, via the Minkowski functional — available as a corollary.
--
--   **Formalization Note.** Positive homogeneity is assumed only for $\alpha > 0$, exactly as in the source; nothing is assumed about $p$ at $\alpha \le 0$. Continuity of the extension is asserted explicitly as part of the conclusion, as the source observes immediately after the proof.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.4, Theorem 1, p. 111

import Mathlib

namespace VectorSpaceOpt

theorem hahn_banach_sublinear {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : X → ℝ) (hp_add : ∀ x y : X, p (x + y) ≤ p x + p y)
    (hp_smul : ∀ a : ℝ, 0 < a → ∀ x : X, p (a • x) = a * p x)
    (hp_cont : Continuous p)
    (M : Submodule ℝ X) (f : M →ₗ[ℝ] ℝ) (hf : ∀ m : M, f m ≤ p m) :
    ∃ F : X →ₗ[ℝ] ℝ, Continuous F ∧ (∀ m : M, F m = f m) ∧ ∀ x : X, F x ≤ p x := by
  sorry

end VectorSpaceOpt
