-- Prove2me | Theorems.Thm_VectorSpaceOpt_eidelheit_separation
-- name    : VectorSpaceOpt.eidelheit_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:53:56.118919+00:00
-- url     : https://prove2.me/theorems/b9a34bff-d867-46f2-adc3-a225d890dad1
-- title:
--   Eidelheit's separation theorem
-- statement:
--   Let $K_1$ and $K_2$ be convex sets in a real normed space $X$, with $K_1$ having **nonempty interior** and $K_2$ nonempty and containing **no interior point** of $K_1$. Then a closed hyperplane separates them: there are a nonzero $x^* \in X^*$ and a constant $c$ with
--
--   $$\sup_{k_1 \in K_1} \langle k_1, x^*\rangle \;\le\; c \;\le\; \inf_{k_2 \in K_2} \langle k_2, x^*\rangle,$$
--
--   so $K_1$ and $K_2$ lie in opposite closed half-spaces of $\{x : \langle x, x^*\rangle = c\}$.
--
--   Two consequences the source draws from it. If $K$ is closed convex and $x \notin K$, then the distance $d$ from $x$ to $K$ is positive, and separating $K$ from the open ball of radius $d/2$ about $x$ produces a closed half-space containing $K$ but not $x$. Iterating over all such $x$ gives the statement that a closed convex set is the **intersection of all closed half-spaces containing it** — which the source calls the geometric foundation of duality theory for convex sets, since it expresses a set in $X$ as a family of elements of $X^*$.
--
--   **Formalization Note.** Separation is stated as the two families of inequalities $\langle k_1, x^*\rangle \le c \le \langle k_2, x^*\rangle$ rather than through suprema, so no boundedness of either side needs to be assumed. Nonemptiness of $K_2$ is explicit; without it the nonzero-functional claim would fail in a trivial space.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.12, Theorem 3, pp. 133–134

import Mathlib

namespace VectorSpaceOpt

theorem eidelheit_separation {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K₁ K₂ : Set X) (h₁ : Convex ℝ K₁) (h₂ : Convex ℝ K₂)
    (hKi : (interior K₁).Nonempty) (hne : K₂.Nonempty)
    (hdisj : K₂ ∩ interior K₁ = ∅) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ k ∈ K₁, f k ≤ c) ∧
      (∀ k ∈ K₂, c ≤ f k) := by sorry

end VectorSpaceOpt
