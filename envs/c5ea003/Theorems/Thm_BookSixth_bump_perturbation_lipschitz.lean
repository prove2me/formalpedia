-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_lipschitz
-- name    : BookSixth.bump_perturbation_lipschitz
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-26T23:06:50.058985+00:00
-- url     : https://prove2.me/theorems/010c4541-a676-4193-a55d-91cea9f7aab8
-- title:
--   A finite bump perturbation is Lipschitz with constant $(L+M)$ per summand
-- statement:
--   Let $\chi_0,\dots,\chi_{n-1}$ be $1$-Lipschitz real-valued functions and $S_0,\dots,S_{n-1}$ be $1$-Lipschitz maps $\mathbb{R}^3\to\mathbb{R}^3$, with $\|\chi_i(x)\|\le L$ for all $x$ and $\|S_i(y)-y\|\le M$ for all $y$. Then the vector field
--
--   $$E(x) = \sum_{i} \chi_i(x)\,\bigl(S_i(x)-x\bigr)$$
--
--   is Lipschitz: each summand contributes at most $(L+M)\,\|x-y\|$, so $\|E(x)-E(y)\| \le \bigl(\sum_i (L+M)\bigr)\,\|x-y\|$.
--
--   The content is a two-term rewriting. Adding and subtracting $\chi_i(x)(S_i(y)-y)$ gives
--
--   $$\chi_i(x)(S_i(x)-x) - \chi_i(y)(S_i(y)-y) = (\chi_i(x)-\chi_i(y))(S_i(y)-y) + \chi_i(x)(S_i(x)-S_i(y)),$$
--
--   in which *every* factor that is subsequently multiplied is bounded: $\|\chi_i(x)\|\le L$ by hypothesis, $\|S_i(x)-S_i(y)\|\le\|x-y\|$ because $S_i$ is $1$-Lipschitz, $\|\chi_i(x)-\chi_i(y)\|\le\|x-y\|$ because $\chi_i$ is $1$-Lipschitz (on $\mathbb{R}$ the norm is the absolute value), and $\|S_i(y)-y\|\le M$ by hypothesis. Hence each summand is at most $(L+M)\,\|x-y\|$.
--
--   The naive splitting $\chi_i(x)S_i(x) - (\chi_i(x))x$ does **not** give this bound, because it requires control of $\|S_i(x)\|$, which is unbounded in $x$; the rewriting above is precisely what removes that unbounded factor. The outer step is subadditivity of the supremum norm over a finite sum.
-- source:
--   Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension. That leaf requires an ambient isotopy which acts as a prescribed positive similarity on each round circle and is the identity near all the others. Writing the ambient map as $F(x) = x + E(x)$ with $E$ as above, and taking the cutoffs $\chi_i$ from Thm_BookSixth_continuous_cutoff (theorem id faf7628a-1f49-4817-ba2b-dd2f26b3689b) on the pairwise disjoint open neighbourhoods supplied by BookSixth.pairwise_disjoint_open_neighbourhoods (theorem id 7fd98b02-98b1-425a-82fb-6b515df86aeb, Proved) and the compactness supplied by BookSixth.round_circle_is_compact (theorem id 447ecc36-9c38-481b-a4f5-9bc76f5c54a6, Proved), this bound is what makes the ambient map invertible: the already-proved BookSixth.small_displacement_is_homeomorph (theorem id 5f342cbf-e04b-4e47-b598-dafa8fe75f19) applies exactly when the displacement constant is less than $1$, which is arranged by subdividing the path in time so that each $S_i$ moves only a little. Every Mathlib ingredient used in the intended proof is at Mathlib c5ea0035: the triangle inequality `norm_add_le` and `norm_sub_le` (Analysis/Normed/Group/Basic.lean:97 and :155), `norm_smul` (Analysis/Normed/MulAction.lean:98), the finite-sum subadditivity `norm_sum_le` (Analysis/Normed/Group/Basic.lean:828), and `Real.norm_eq_abs` (Analysis/Normed/Group/Real.lean:55).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_lipschitz (n : ℕ) (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i)) (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i)) (hSiy : ∀ i y, ‖S i y - y‖ ≤ M) : ∀ x y : Space3, ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ (∑ i : Fin n, (L + M)) * ‖x - y‖ := by sorry
