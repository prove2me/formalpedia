-- Prove2me | Theorems.Thm_abs_quad_form_entry_perturbation
-- name    : abs_quad_form_entry_perturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:16:27.57366+00:00
-- url     : https://prove2.me/theorems/6d918fbd-f9fe-42b1-9f72-4d30de555432
-- title:
--   Entrywise perturbation of a quadratic form: $|z^{\mathsf T}\Delta z| \le \varepsilon n \sum z_i^2$
-- statement:
--   An entrywise perturbation of a matrix changes every quadratic form by at most $\varepsilon n \sum_i z_i^2$.
--
--   Let $R$ be a linearly ordered field, $\Delta$ an $n\times n$ matrix over $R$, and suppose every entry satisfies $|\Delta_{ij}|\le \varepsilon$ with $\varepsilon\ge 0$. Then for every $z\in R^n$,
--
--   $$\bigl|\,z^{\mathsf T}\Delta z\,\bigr|\ \le\ \varepsilon\,n\,\sum_{i=1}^n z_i^2 .$$
--
--   **Proof shape.** Split the quadratic form as a double sum, bound $|\Delta_{ij}|\le\varepsilon$ entrywise, and factor: $\sum_{i,j}\varepsilon|z_i||z_j|=\varepsilon\bigl(\sum_i|z_i|\bigr)^2$; then use the $\ell^1$–$\ell^2$ comparison $\bigl(\sum_i|z_i|\bigr)^2\le n\sum_i z_i^2$.
--
--   **Role.** This is the standard robustness step that turns an exactly-computed (rational) PSD certificate into a statement about a nearby true matrix: if $X$ is certified to have $z^{\mathsf T}Xz\ge -\delta\sum z_i^2$ and a computation perturbs it entrywise by at most $\varepsilon$, then the perturbed matrix satisfies $z^{\mathsf T}X'z\ge -(\delta+\varepsilon n)\sum z_i^2$ — so margins degrade by $\varepsilon n$, not by an uncontrolled amount. It is the inequality that lets an exact-arithmetic optimisation loop be analysed as if it ran in real arithmetic, with an explicit, quantitative error budget.
-- source:
--   Standard perturbation lemma used in the numerical analysis of semidefinite relaxations; internal accounting lemma of the Quantum Max-Cut 0.53 formalisation.

import Mathlib
open Matrix

theorem abs_quad_form_entry_perturbation {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |z ⬝ᵥ (Δ *ᵥ z)| ≤ ε * (n : R) * ∑ i, z i ^ 2 := by sorry
