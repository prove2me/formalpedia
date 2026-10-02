-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_is_homeomorph_v2
-- name    : BookSixth.bump_perturbation_is_homeomorph_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T00:56:43.605584+00:00
-- url     : https://prove2.me/theorems/24b19980-6e94-419a-9d06-7dfe31dd0562
-- title:
--   A small bump perturbation of the identity is a homeomorphism (corrected criterion)
-- statement:
--   Let $\chi_0,\dots,\chi_{n-1}:\mathbb{R}^3\to\mathbb{R}$ be $1$-Lipschitz real functions with $|\chi_i|\le L$, and let $S_0,\dots,S_{n-1}:\mathbb{R}^3\to\mathbb{R}^3$ be continuous $1$-Lipschitz maps moving every point by at most $q\ge 0$. Assume
--
--   $$n\,(2L+q) < 1.$$
--
--   Then the map
--
--   $$F(x) = x + \sum_{i} \chi_i(x)\,\bigl(S_i(x)-x\bigr)$$
--
--   is a homeomorphism of $\mathbb{R}^3$: it is continuous and has a continuous inverse.
--
--   **The bound $n(2L+q)<1$ is the essential hypothesis, and it is not implied by $q<1$.** The displacement $E(x)=\sum_i \chi_i(x)(S_i(x)-x)$ is Lipschitz with constant $n(2L+q)$: for a single summand, adding and subtracting $\chi_i(y)(S_i(x)-x)$ gives
--
--   $$\chi_i(x)(S_i(x)-x)-\chi_i(y)(S_i(y)-y) = (\chi_i(x)-\chi_i(y))(S_i(x)-x) + \chi_i(y)\bigl[(S_i(x)-x)-(S_i(y)-y)\bigr],$$
--
--   whose two terms are bounded by $\|x-y\|\,q$ and $L\cdot 2\|x-y\|$, since a $1$-Lipschitz map has a **$2$-Lipschitz** displacement. Hence $\|E(x)-E(y)\|\le n(2L+q)\,\|x-y\|$, and when that constant is below $1$ the map $x\mapsto x+E(x)$ is a bijection with continuous inverse.
--
--   Without the bound the statement is false, and the factor $n$ is not decorative. For a counterexample to the version assuming only $q<1$, take $n=8$, $L=q=\tfrac12$, $\chi_i(x)=(\tfrac12)\sin x_1$ and $S_i(x)=x+(\tfrac12,0,0)$. All hypotheses of that weaker version hold, but then $F_1(t)=t+2\sin t$, whose derivative $1+2\cos t$ changes sign at $t=2\pi/3$, so $F$ is not injective. Likewise the bound $2L$ rather than $L$ is forced, for the same reason: the displacement $S_i-\mathrm{id}$ of a $1$-Lipschitz map is $2$-Lipschitz, not $1$-Lipschitz.
-- source:
--   Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension. That leaf needs an ambient isotopy acting as a prescribed positive similarity on each round circle and the identity near all the others. Writing it as $F(x)=x+E(x)$ with $E(x)=\sum_i \chi_i(x)(S_i(x)-x)$, and taking the cutoffs from Thm_BookSixth_continuous_cutoff (theorem id faf7628a-1f49-4817-ba2b-dd2f26b3689b) on the disjoint open neighbourhoods of BookSixth.pairwise_disjoint_open_neighbourhoods (theorem id 7fd98b02-98b1-425a-82fb-6b515df86aeb, Proved) over the compact components of BookSixth.round_circle_is_compact (theorem id 447ecc36-9c38-481b-a4f5-9bc76f5c54a6, Proved), this is the step that yields a genuine homeomorphism. The analytic core is proved on the platform as BookSixth.small_displacement_is_homeomorph (theorem id 5f342cbf-e04b-4e47-b598-dafa8fe75f19, Proved), which returns a continuous two-sided inverse for a displacement of Lipschitz constant $<1$; the companion estimate is BookSixth.bump_perturbation_lipschitz_v2 (theorem id 00c3e7a7-f202-4293-aafe-919f3115ddd3), whose per-summand constant is $\lvert\chi_i x-\chi_i y\rvert\le\lvert x-y\rvert$ times $\|S_ix-x\|\le q$, plus $\lvert\chi_i y\rvert\le L$ times the $\|(S_ix-x)-(S_iy-y)\|\le 2\|x-y\|$ bound. **This statement corrects BookSixth.bump_perturbation_is_homeomorph (theorem id 09df5389-102b-4570-953d-0524cc60c3c7), which assumed only $q<1$ and is FALSE**, as the counterexample in the natural-language statement shows. It also supersedes BookSixth.bump_perturbation_lipschitz (theorem id 010c4541-a676-4193-a55d-91cea9f7aab8), which claimed the constant $L+M$ and is likewise false; the sharp constant is $2L+M$.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_is_homeomorph_v2 (n : ℕ) (L : ℝ) (hL : 0 ≤ L) (q : ℝ) (hq : 0 ≤ q) (hLip : n * (2 * L + q) < 1) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i)) (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i)) (hqL : ∀ i x, ‖S i x - x‖ ≤ q) (hcont : ∀ i, Continuous (S i)) (hchiC : ∀ i, Continuous (chi i)) : ∃ F : Space3 → Space3, Continuous F ∧ ∃ Finv : Space3 → Space3, Continuous Finv ∧ ∀ x, Finv (F x) = x ∧ ∀ x, F (Finv x) = x ∧ ∀ x, F x = x + ∑ i, chi i x • (S i x - x) := by sorry
