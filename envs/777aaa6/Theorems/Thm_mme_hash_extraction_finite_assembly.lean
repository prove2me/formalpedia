-- Prove2me | Theorems.Thm_mme_hash_extraction_finite_assembly
-- name    : mme_hash_extraction_finite_assembly
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T09:00:45.852995+00:00
-- url     : https://prove2.me/theorems/6c1c6f8d-58c8-48df-b7a6-848c8a2b7786
-- title:
--   Hash bundles: finite extraction with certified volume
-- statement:
--   Let $D$ be a finite hash bundle with per-factor lower counts $L_j$, positive repair grouping cost $H$, common matrix dimensions $a,b,c$, and source power $s$. Suppose every hash factor satisfies its ambient-degree and usable-incidence budgets, and the bundle's algebraic realization predicate holds over a field $K$.
--
--   For every real $\tau$, there is an actual finite direct sum of matrix multiplication tensors restricting from $\operatorname{sym}_6(CW_5^{\otimes4})^{\otimes s}$ whose total $\tau$-volume is at least
--
--   $$\left(\frac{\prod_j L_j}{H}-1\right)(abc)^\tau.$$
--
--   This assembly theorem combines same-state usable-copy selection with the assumed actual tensor realization and includes the loss from grouping an integer number of copies for repair. It does not prove the realization predicate or the concrete budgets.
-- source:
--   Finite assembly consequence of the companion usable-isolation theorem and the definition mme_hash_extraction_certificate; motivated by arXiv:2404.16349v2 Sections 5--6. https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_hash_extraction_certificate
open BigOperators MME MME.RecursiveXHash MME.HashExtraction
set_option autoImplicit false
universe u

theorem mme_hash_extraction_finite_assembly {K : Type u} [Field K] (d : Data) (tau : ℝ)
    (hbudget : ∀ j, (d.hash j).Budget) (hsource : d.Realizes K) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((sixSymmetrization (MME.StothersFourth.cwFourthObj K 5)).kronPow d.power) ∧
      d.rate tau ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
