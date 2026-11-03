-- Prove2me | Theorems.Thm_FSCofinality_coset_cofinality
-- name    : FSCofinality.coset_cofinality
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T12:41:04.030953+00:00
-- url     : https://prove2.me/theorems/43151303-0fcb-4d53-ab4f-209a62939fdb
-- title:
--   Theorem 4.1 — Polishable coset relations above every countable level
-- statement:
--   For every countable ordinal a, there are a closed subgroup G of the full permutation group of the natural numbers and a continuous injective homomorphism pi from G to that permutation group such that the product-limit Friedman--Stanley relation J_a Borel reduces to the coset relation of the image pi[G]. The image is Borel. Its Polishability is represented by the closed Polish source group and continuous injective homomorphism data; the transported group topology need not equal the ambient subspace topology. The subgroup and homomorphism may depend separately on a.
--
--   For every $\alpha<\omega_1$ there are closed $G\le S_\infty$ and continuous injective $\pi:G\to S_\infty$ with Borel image and $$\mathsf J_\alpha\leq_B E_{\pi[G]},\qquad pE_{\pi[G]}q\ \Longleftrightarrow\ q^{-1}p\in\pi[G].$$
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Theorem 4.1 (coset cofinality), lines 816--826; construction completed in Section 4.7.

import Definitions.Def_FSCofinalityHierarchy20261102
import Definitions.Def_FSCofinalityCosets20261102

set_option autoImplicit false

theorem FSCofinality.coset_cofinality
    (a : Ordinal.{0}) (ha_countable : a < Ordinal.omega 1) :
    ∃ G : Subgroup FSCofinality.PermutationGroup,
      IsClosed (G : Set FSCofinality.PermutationGroup) ∧
      ∃ π : G →* FSCofinality.PermutationGroup,
        Continuous π ∧ Function.Injective π ∧
        MeasurableSet (π.range : Set FSCofinality.PermutationGroup) ∧
        (FSCofinality.fsTower a).Reduces (FSCofinality.imageCosetRelation π) := by sorry
