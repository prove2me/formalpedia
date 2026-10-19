-- Prove2me | Theorems.Thm_AbelianTargets_exists_anisotropic_scales
-- name    : AbelianTargets.exists_anisotropic_scales
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:37.864081+00:00
-- url     : https://prove2.me/theorems/9a507cef-d67d-4d92-8790-4314df516902
-- title:
--   Successive choice of anisotropic scales
-- statement:
--   Let $A\in\mathbb R$, let $B:\mathbb N\to\mathbb R$ be arbitrary, and let $L_0,M_0\in\mathbb N$. For every $\varepsilon>0$ there are natural numbers $L,M$ such that
--   $$
--   L\ge\max(1,L_0),\qquad M\ge\max(1,M_0),\qquad
--   \frac{A\log(L+2)}{L}+\frac{B(L)}{M}<\varepsilon.
--   $$
--   There is no positivity or growth assumption on $A$ or $B$. The first scale is selected before its finite transverse bound $B(L)$ is evaluated. This permits arbitrarily fast dependence of that bound on the first scale.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 6, Proposition 6.1; https://arxiv.org/html/2609.39824v1#S6. Auxiliary formalization result in original module AbelianTargets/AnisotropicScales.lean, authoritative declaration span lines 25-55, SHA-256 36e4dd3474b95b9740ec13a9a593ecd430f0e58fe6fa5a6b6f777472a056b53a. Frozen original source is local; no public repository URL or commit was available.

import Init
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Successive scale choice in Proposition 6.1

After the first scale is chosen, an arbitrary finite transverse bound
depending on that scale can be made small by a second scale. No uniform
bound in the first scale is assumed or needed.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology

theorem AbelianTargets.exists_anisotropic_scales (A : ℝ) (B : ℕ → ℝ)
    (L₀ M₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L M : ℕ, 1 ≤ L ∧ L₀ ≤ L ∧ 1 ≤ M ∧ M₀ ≤ M ∧
      A * Real.log ((L : ℝ) + 2) / (L : ℝ) + B L / (M : ℝ) < ε := by sorry
