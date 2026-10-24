-- Prove2me | Theorems.Thm_NoUniversalFSigma_no_universal_fsigma
-- name    : NoUniversalFSigma.no_universal_fsigma
-- status  : Proved
-- author  : @username
-- created : 2026-10-23T06:25:43.935321+00:00
-- url     : https://prove2.me/theorems/501a3bf8-ab5a-4d8f-b7da-eb7f16dbd9ac
-- title:
--   Theorem 1.1 — no universal $F_\sigma$ equivalence relation
-- statement:
--   For every Polish space $Y$, there is no equivalence relation $F$ on $Y$ whose graph is $F_\sigma$ and which is universal under Borel reducibility for all $F_\sigma$ equivalence relations on Polish spaces. Explicitly,
--   $$\neg\exists F\;\bigl[F\text{ is an }F_\sigma\text{ equivalence relation on }Y\ \land\ \forall(X,E)\;E\leq_B F\bigr],$$
--   where $(X,E)$ ranges over Polish spaces and $F_\sigma$ equivalence relations on them. A Borel reduction is a Borel measurable map preserving and reflecting equivalence. This is the final assertion of Theorem 1.1.
--
--   **Formalization Note** Source and target spaces range over the ordinary Lean type universe; it includes real $\ell_2$ and the standard presentations of Polish spaces.
-- source:
--   Ruijun Wang, There is no universal F_sigma equivalence relation, arXiv:2610.31052v1 (22 October 2026), Theorem 1.1, final assertion, Section 1, https://arxiv.org/html/2610.31052v1

import Definitions.Def_NoUniversalFSigma261031052

set_option autoImplicit false

/-- Theorem 1.1 of arXiv:2610.31052v1, final nonuniversality assertion. -/

theorem NoUniversalFSigma.no_universal_fsigma
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] :
    ¬ ∃ F : Setoid Y,
      NoUniversalFSigma.IsFSigmaRelation F.r ∧
      NoUniversalFSigma.IsUniversalFSigma F.r := by sorry
