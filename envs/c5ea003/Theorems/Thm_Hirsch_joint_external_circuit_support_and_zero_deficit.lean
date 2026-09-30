-- Prove2me | Theorems.Thm_Hirsch_joint_external_circuit_support_and_zero_deficit
-- name    : Hirsch.joint_external_circuit_support_and_zero_deficit
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T23:57:45.721189+00:00
-- url     : https://prove2.me/theorems/215a5bbf-fda4-467b-9e99-8714e6ec007b
-- title:
--   External joint-allocation circuits: exact support multipliers and zero-deficit rigidity
-- statement:
--   Let there be finitely many original rows and finitely many finite candidate lists, each with an anchor at zero. Let $a_{i\ell j}$ be the evaluation of original row $i$ on listed generator $j$ of block $\ell$. A nonnegative multiplier $(\lambda,\mu,\nu)$ satisfies $-\sum_i\lambda_i a_{i\ell j}-\mu_{\ell j}+\nu_\ell=0$ for every block and generator. Assume some original-row weight is nonzero, and its support is minimal among all nonzero nonnegative multipliers satisfying these same null equations.
--
--   For every block the total multiplier is an attained maximum:
--
--   $$\nu_\ell=\max\{0,\max_j\sum_i\lambda_i a_{i\ell j}\}.$$
--
--   For any nonnegative row bounds $h_i$ dominating every listed evaluation in that block, define $\Gamma_\ell=\sum_i\lambda_i h_i-\nu_\ell$. Then $\Gamma_\ell\ge0$, and
--
--   $$\Gamma_\ell=0\quad\Longleftrightarrow\quad\text{one listed point, possibly the anchor, attains every }h_i\text{ with }\lambda_i>0.$$
--
--   This derives the coefficient signs and exact zero pattern needed for joint packing inequalities. It does not construct a complete circuit catalogue, prove an optimizer correct, or bound a polytope's ordinary-edge diameter.
--
--   **Formalization Note** The maximum is expressed by nonnegativity, finitely many upper bounds, and attainment. Generator lists may be dependent, repeated, or empty; the anchor remains present.
-- source:
--   Nonnegative support argument in jjoshua2/prove2me-work, research/FINITE_SUMMAND_PACKING_2026-09-13.md, section 4, at commit 11172b1165b31a81e8755bd9f88651a2a9ed4b8c. Full proof and added zero-deficit derivation: research/JOINT_CIRCUIT_SUPPORT_2026-09-13.md, sections 2-4, in this continuation bundle. No historical novelty claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.joint_external_circuit_support_and_zero_deficit
    (m r k : ℕ) (a : Fin m → Fin r → Fin k → ℝ)
    (w : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ)
    (hw : ∀ q, 0 ≤ w q)
    (hkernel : ∀ l j, -(∑ i, w (.inl i) * a i l j) -
      w (.inr (l, some j)) + w (.inr (l, none)) = 0)
    (hexternal : ∃ i, w (.inl i) ≠ 0)
    (hminimal : ∀ y : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ,
      (∀ q, 0 ≤ y q) →
      (∀ l j, -(∑ i, y (.inl i) * a i l j) -
        y (.inr (l, some j)) + y (.inr (l, none)) = 0) →
      y ≠ 0 → Function.support y ⊆ Function.support w →
        Function.support w ⊆ Function.support y) :
    ∀ l,
      (0 ≤ w (.inr (l, none)) ∧
        (∀ j, (∑ i, w (.inl i) * a i l j) ≤ w (.inr (l, none))) ∧
        (w (.inr (l, none)) = 0 ∨
          ∃ j, w (.inr (l, none)) = ∑ i, w (.inl i) * a i l j)) ∧
      ∀ h : Fin m → ℝ, (∀ i, 0 ≤ h i) → (∀ i j, a i l j ≤ h i) →
        0 ≤ (∑ i, w (.inl i) * h i) - w (.inr (l, none)) ∧
        (((∑ i, w (.inl i) * h i) - w (.inr (l, none)) = 0) ↔
          ∃ q : Option (Fin k), ∀ i, 0 < w (.inl i) →
            (match q with | none => 0 | some j => a i l j) = h i) := by sorry
