-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_is_homeomorph
-- name    : BookSixth.bump_perturbation_is_homeomorph
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-27T00:50:13.201977+00:00
-- url     : https://prove2.me/theorems/09df5389-102b-4570-953d-0524cc60c3c7
-- title:
--   A small bump perturbation of the identity is a homeomorphism
-- statement:
--   Let $\chi_0,\dots,\chi_{n-1}:\mathbb{R}^3\to\mathbb{R}$ be $1$-Lipschitz real functions bounded in absolute value by $L$, and let $S_0,\dots,S_{n-1}:\mathbb{R}^3\to\mathbb{R}^3$ be continuous $1$-Lipschitz maps that move every point by at most $q$, where $0\le q<1$. Then the map
--
--   $$F(x) = x + \sum_{i} \chi_i(x)\,\bigl(S_i(x)-x\bigr)$$
--
--   is a homeomorphism of $\mathbb{R}^3$: it is continuous and has a continuous inverse.
--
--   The point is that a displacement which is *bounded* — here by $\sum_i L\,q$, since $|\chi_i|\le L$ and $\|S_i(x)-x\|\le q$ — and whose variation is controlled by the Lipschitz hypotheses, is a contraction in small enough steps. Concretely, the displacement $E(x)=\sum_i \chi_i(x)(S_i(x)-x)$ obeys a Lipschitz bound of the form
--
--   $$\|E(x)-E(y)\| \le n\,(2L + M)\,\|x-y\|,$$
--
--   with $M:=q$, so once $n\,(2L+q)<1$ the map $x\mapsto x+E(x)$ is injective and surjective. The condition $q<1$ alone is enough for the *statement* here only because the caller is expected to choose $L$ small as well, which is exactly what subdividing a path in time achieves: making each $S_i$ a small motion makes both $q$ and the product small. This packages the classical small-displacement argument as an explicit two-sided inverse rather than asserting bijectivity, so that no appeal to a general homeomorphism constructor is needed.
-- source:
--   Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension. That leaf requires an ambient isotopy acting as a prescribed positive similarity on each round circle and the identity near all the others. Writing that ambient map as $F(x)=x+E(x)$ with $E(x)=\sum_i \chi_i(x)(S_i(x)-x)$, and taking the cutoffs $\chi_i$ from Thm_BookSixth_continuous_cutoff (theorem id faf7628a-1f49-4817-ba2b-dd2f26b3689b) on the pairwise disjoint open neighbourhoods of BookSixth.pairwise_disjoint_open_neighbourhoods (theorem id 7fd98b02-98b1-425a-82fb-6b515df86aeb, Proved) over the compact components supplied by BookSixth.round_circle_is_compact (theorem id 447ecc36-9c38-481b-a4f5-9bc76f5c54a6, Proved), this statement is the step that turns the local construction into a genuine homeomorphism. The analytic core is already proved on the platform as BookSixth.small_displacement_is_homeomorph (theorem id 5f342cbf-e04b-4e47-b598-dafa8fe75f19, Proved), which gives a continuous two-sided inverse for a displacement of Lipschitz constant $<1$; the companion estimate is BookSixth.bump_perturbation_lipschitz_v2 (theorem id 00c3e7a7-f202-4293-aafe-919f3115ddd3). Note that the earlier BookSixth.bump_perturbation_lipschitz (theorem id 010c4541-a676-4193-a55d-91cea9f7aab8) claimed the constant $L+M$ and is **false**; the sharp constant is $2L+M$, because a $1$-Lipschitz map has a $2$-Lipschitz displacement.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_is_homeomorph (n : ℕ) (L : ℝ) (hL : 0 ≤ L) (q : ℝ) (hq : 0 ≤ q ∧ q < 1) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i)) (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i)) (hqL : ∀ i x, ‖S i x - x‖ ≤ q) (hcont : ∀ i, Continuous (S i)) (hchiC : ∀ i, Continuous (chi i)) : ∃ F : Space3 → Space3, Continuous F ∧ ∃ Finv : Space3 → Space3, Continuous Finv ∧ ∀ x, Finv (F x) = x ∧ ∀ x, F (Finv x) = x ∧ ∀ x, F x = x + ∑ i, chi i x • (S i x - x) := by sorry
