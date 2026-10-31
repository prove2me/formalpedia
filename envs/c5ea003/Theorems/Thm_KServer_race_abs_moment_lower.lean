-- Prove2me | Theorems.Thm_KServer_race_abs_moment_lower
-- name    : KServer.race_abs_moment_lower
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T16:41:15.73233+00:00
-- url     : https://prove2.me/theorems/99f9571c-b22c-431d-a5e2-d6fddb3681a5
-- title:
--   A finite weighted second–fourth moment lower bound on mean absolute size
-- statement:
--   Let $\Omega$ be a finite set, let $P_\omega\ge0$ be weights, and let $Z:\Omega\to\mathbb R$. For $s>0$, suppose
--
--   $$\sum_\omega P_\omega Z_\omega^2\ge\frac{s^2}{4},\qquad \sum_\omega P_\omega Z_\omega^4\le4s^4.$$
--
--   Then
--
--   $$\sum_\omega P_\omega|Z_\omega|\ge\frac{s}{50}.$$
--
--   The weights need not sum to one. This quantitative moment estimate supplies an absolute-imbalance gain in the BCR race accounting, and also applies to any finite weighted statistic with the stated moment bounds.
--
--   **Formalization Note** The constants are deliberately loose; this is an elementary sufficient inequality, not the central-limit theorem used in the source paper.
-- source:
--   Bubeck, Coester and Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1 (stages 1–3), Section 4.2, equations (3) and (4), printed pp. 16–19. Original elementary moment inequality for the absolute-imbalance term in equation (3); the displayed constants are derived here and are not quoted from the paper.

import Mathlib
open scoped BigOperators

theorem KServer.race_abs_moment_lower {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Z : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (s : ℝ) (hs : 0 < s)
    (hsecond : s ^ 2 / 4 ≤ ∑ ω, P ω * Z ω ^ 2)
    (hfourth : (∑ ω, P ω * Z ω ^ 4) ≤ 4 * s ^ 4) :
    s / 50 ≤ ∑ ω, P ω * |Z ω| := by sorry
