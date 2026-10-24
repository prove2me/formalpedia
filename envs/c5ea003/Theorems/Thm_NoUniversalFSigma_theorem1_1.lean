-- Prove2me | Theorems.Thm_NoUniversalFSigma_theorem1_1
-- name    : NoUniversalFSigma.theorem1_1
-- status  : Proved
-- author  : @username
-- created : 2026-10-23T06:26:15.190291+00:00
-- url     : https://prove2.me/theorems/6d0bffa2-86f8-40bb-a3b2-300b3cc91b85
-- title:
--   Theorem 1.1 — an $F_\sigma$ linear-subspace obstruction for every target
-- statement:
--   Let $Y$ be any Polish space and let $F$ be any equivalence relation on $Y$ whose graph is $F_\sigma$. There is a real linear subspace $H\subseteq\ell_2$ such that $H$ is $F_\sigma$, its coset equivalence relation $xE_Hx'\iff x-x'\in H$ has an $F_\sigma$ graph, and
--   $$\neg\exists f:\ell_2\to Y\quad\bigl[f\text{ is Baire measurable}\ \land\ \forall x,x'\in\ell_2,\ (x-x'\in H\iff F(f(x),f(x')))\bigr].$$
--   The norm topology is used on real $\ell_2$. The subspace is not required to be closed or Polish. Empty target spaces are included, and the target space may lie in any Lean universe. This is the full existence assertion of Theorem 1.1; the separate nonuniversality target records its concluding consequence.
-- source:
--   Ruijun Wang, There is no universal F_sigma equivalence relation, arXiv:2610.31052v1 (22 October 2026), Theorem 1.1, main existence assertion, Section 1, https://arxiv.org/html/2610.31052v1

import Definitions.Def_NoUniversalFSigma261031052

set_option autoImplicit false

universe u

/-- Theorem 1.1 of arXiv:2610.31052v1, main existence assertion. -/

theorem NoUniversalFSigma.theorem1_1
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : NoUniversalFSigma.IsFSigmaRelation F.r) :
    ∃ H : Submodule ℝ NoUniversalFSigma.RealL2,
      NoUniversalFSigma.IsFSigma (H : Set NoUniversalFSigma.RealL2) ∧
      NoUniversalFSigma.IsFSigmaRelation (NoUniversalFSigma.CosetRelation H) ∧
      ¬ ∃ f : NoUniversalFSigma.RealL2 → Y,
        NoUniversalFSigma.IsBaireMeasurable f ∧
        NoUniversalFSigma.IsReduction f (NoUniversalFSigma.CosetRelation H) F.r := by sorry
