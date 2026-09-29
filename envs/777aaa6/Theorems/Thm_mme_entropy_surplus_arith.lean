-- Prove2me | Theorems.Thm_mme_entropy_surplus_arith
-- name    : mme_entropy_surplus_arith
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T07:23:20.255659+00:00
-- url     : https://prove2.me/theorems/cf6fdb68-c5b0-4c40-9ea0-70f66890ea30
-- title:
--   Numerical surplus inequality for five copies at dimensions 25
-- statement:
--   Let $tau = 3952233/5000000$. Then $$49 < 5 * 25^{tau}.$$ This is the numerical surplus used by the $N=2$, $inputs=1$, $outputs=5$, $M=25$ entropy-recipe witness, since $1 * 7^2 = 49$. The bound holds with about thirty percent margin and is independent of any recipe construction.
--
--   **Formalization Note** Lean states the inequality with natural-number casts to reals and real exponentiation.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . This child isolates the numerical surplus inequality; the recipe witness is a separate child.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_surplus_arith : ((49 : ℕ) : ℝ) < ((5 : ℕ) : ℝ) * (((25 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by sorry
