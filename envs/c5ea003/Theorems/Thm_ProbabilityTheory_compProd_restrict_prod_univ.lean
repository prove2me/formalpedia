-- Prove2me | Theorems.Thm_ProbabilityTheory_compProd_restrict_prod_univ
-- name    : ProbabilityTheory.compProd_restrict_prod_univ
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T17:12:50.41267+00:00
-- url     : https://prove2.me/theorems/4c8f7d4e-879b-48b8-97a6-b146180b8bb9
-- title:
--   Restricting a composition-product to a cylinder over the first coordinate
-- statement:
--   Restricting a joint law to an event that depends only on the first coordinate is the same as restricting the first marginal.
--
--   Let $\mu$ be an s-finite measure on $\mathcal A$ and $\kappa$ an s-finite kernel from $\mathcal A$ to $\mathcal B$, and let $s\subseteq\mathcal A$ be measurable. Then
--
--   $$
--   \big(\mu\otimes\kappa\big)\big|_{s\times\mathcal B} \;=\; \big(\mu|_{s}\big)\otimes\kappa .
--   $$
--
--   The event $s\times\mathcal B$ constrains only the first coordinate, so cutting the joint law down to it and cutting the first marginal down to $s$ before composing produce the same measure — the kernel is untouched either way.
--
--   This is the form in which one localises a two-stage experiment to an event decided at the first stage: for instance, restricting attention to the histories on which a stopping time has not yet fired before analysing the next round.
--
--   **Formalization Note** Mathlib has the analogous statement for `Kernel.compProd`; this is the version for a measure composed with a kernel. Only s-finiteness is needed, so it applies to the sub-probability measures produced by restriction.
-- source:
--   Standard property of the composition-product of a measure with a kernel; the analogue for Kernel.compProd is ProbabilityTheory.Kernel.compProd_restrict in Mathlib. Used to localise the canonical bandit model of Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, Section 4.6, printed pp. 48-50, to an event of the past.

import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem ProbabilityTheory.compProd_restrict_prod_univ {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ (Set.univ : Set β)) = (μ.restrict s) ⊗ₘ κ := by
  sorry
