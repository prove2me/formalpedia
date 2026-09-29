-- Prove2me | Theorems.Thm_finite_linear_gaps_stable
-- name    : finite_linear_gaps_stable
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:31:34.378155+00:00
-- url     : https://prove2.me/theorems/da952638-9e82-4695-befe-207d492be2cf
-- title:
--   Finitely many positive linear gaps are stable under small perturbations
-- statement:
--   Let $C$ and $I$ be finite index sets. Suppose every linear functional $A_c$ has value at least $\varepsilon>0$ at $u$. Then all these gaps remain at least $\varepsilon/2$ after a sufficiently small perturbation in a fixed direction $q$:
--
--   $$
--   \exists\delta>0\;\forall |\Delta|\le\delta\;\forall c\in C,
--   \qquad
--   \sum_{i\in I}A_{c,i}(u_i+\Delta q_i)\ge\frac{\varepsilon}{2}.
--   $$
--
--   The radius is uniform over the finite family. This packages the Hölder/triangle-inequality stability step used when perturbing stochastic bandit environments.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 3, printed p. 490: the bounds following Eq. (37.9), where the loss gap decreases by at most Δ times an ℓ1 norm.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem finite_linear_gaps_stable
    {C I : Type*} [Fintype C] [Fintype I]
    (A : C → I → ℝ) (u q : I → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ c : C, ε ≤ ∑ i, A c i * u i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ → ∀ c : C,
      ε / 2 ≤ ∑ i, A c i * (u i + Δ * q i) := by sorry
