-- Prove2me | Theorems.Thm_BookSixth_round_circle_family_contraction_budget
-- name    : BookSixth.round_circle_family_contraction_budget
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T03:43:23.549183+00:00
-- url     : https://prove2.me/theorems/a4a60e23-7dd9-45b9-b4f3-b03d0a056fab
-- title:
--   Chapter 15: per-component centred contractions satisfy a uniform displacement budget
-- statement:
--   Let $m$ be finite, let $c_1,\dots,c_m\in\mathbb{R}^3$, let $R>0$, and let $a_1,\dots,a_m\in(0,1]$ satisfy $\sum_i (1-a_i)<\tfrac12$. Let $\chi_i:\mathbb{R}^3\to\mathbb{R}$ be continuous cut-offs which are exactly $1$ on the ball $B(c_i,R/2)$ and exactly $0$ outside $B(c_i,5R/2)$, and let $S_i$ be the centred contraction $S_i x = c_i + a_i (x-c_i)$. Then the displacement field $E(x)=\sum_i \chi_i(x)\,(S_i(x)-x)$ is Lipschitz on $\mathbb{R}^3$ with $\operatorname{Lip}(E)\le 2\sum_i(1-a_i)$, and this constant is strictly less than $1$.
--
--   This is the single quantitative estimate that the cut-off patching route to Chapter 15, Theorem 1 requires. The proved theorem `BookSixth.bump_perturbation_is_homeomorph_v4` turns any displacement field that is $q$-Lipschitz with $q<1$ into a homeomorphism of $\mathbb{R}^3$ with continuous inverse, which is exactly the hypothesis that route is otherwise missing, and no theorem in the catalogue currently supplies it.
--
--   The two bounds that do exist, `BookSixth.bump_perturbation_lipschitz_v3` and `BookSixth.bump_perturbation_lipschitz`, bound the field by a sum of per-component displacement radii and cut-off Lipschitz constants. That sum grows both with the size of the family and with the width of the cut-offs, so it cannot fall below $1$ for a large family or for wide cut-offs. Centring each contraction at its own component removes the dependence on both: the derivative of $S_i$ is the scalar $a_i$ and the constant term is absorbed by the centre $c_i$, so each component contributes exactly the scalar deficit $1-a_i$ and only the deficit sum survives. The content of the bound is therefore that the controlling invariant is $\sum_i(1-a_i)$ and not $\sum_i\|S_i-\mathrm{id}\|$.
-- source:
--   Quantitative budget for the cut-off patching route to Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.
--
--   The proved theorem `BookSixth.bump_perturbation_is_homeomorph_v4` (601dd0fa-f3da-4deb-ad08-7ed1bdbfa7eb) accepts any displacement field that is $q$-Lipschitz for some $q<1$ and demands only that each $\chi_i$ and each $S_i$ be continuous, so one such bound closes the whole quantitative step of that route. No theorem in the catalogue provides it: `BookSixth.bump_perturbation_lipschitz_v3` (75689270-e72e-482b-84e9-09a60a3a3a0e) and `BookSixth.bump_perturbation_lipschitz` (010c4541-a676-4193-a55d-91cea9f7aab8) both bound the field by a sum of per-component terms built from the displacement radius and the cut-off Lipschitz constant, and that sum is not uniformly below $1$.
--
--   This child isolates the correct invariant by centring each contraction at its own component, so that the derivative of $S_i$ is the scalar $a_i$ and no constant survives; the Lipschitz constant of the field is then controlled by the deficit sum $\sum_i(1-a_i)$ alone. It is the one remaining obligation on the route from `BookSixth.perfect_circles_pairwise_unlinked_motion` (f6a7245e-187d-4a69-8b49-100cf7e4a1cc), whose catalogue frontier is otherwise a single leaf. The route deliberately avoids `BookSixth.round_circle_prefix_supported_v2` (0e8688d8-cc38-4cb2-bc21-8a74bd34808e), which is authoritatively Disproved.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_family_contraction_budget {m : ℕ} (c : Fin m → Space3) (R : ℝ) (hR : 0 < R)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (hsum : ∑ i, (1 - a i) < 1 / 2)
    (chi : Fin m → Space3 → ℝ) (S : Fin m → Space3 → Space3)
    (hchi : ∀ i, Continuous (chi i))
    (hone : ∀ i x, ‖x - c i‖ ≤ R / 2 → chi i x = 1)
    (hzero : ∀ i j x, i ≠ j → ‖x - c j‖ ≥ 5 * R / 2 → chi i x = 0)
    (hS : ∀ i, Continuous (S i))
    (hcen : ∀ i x, S i x - x = (a i - 1) • (x - c i)) :
    ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖
        ≤ 2 * (∑ i, (1 - a i)) * ‖x - y‖ := by sorry
