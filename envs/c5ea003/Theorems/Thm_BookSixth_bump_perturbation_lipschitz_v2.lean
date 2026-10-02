-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_lipschitz_v2
-- name    : BookSixth.bump_perturbation_lipschitz_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T23:35:16.151986+00:00
-- url     : https://prove2.me/theorems/00c3e7a7-f202-4293-aafe-919f3115ddd3
-- title:
--   A finite bump perturbation is Lipschitz with constant $(2L+M)$ per summand
-- statement:
--   Let $\chi_0,\dots,\chi_{n-1}$ be $1$-Lipschitz real-valued functions and $S_0,\dots,S_{n-1}$ be $1$-Lipschitz maps $\mathbb{R}^3\to\mathbb{R}^3$, with $\|\chi_i(x)\|\le L$ and $\|S_i(y)-y\|\le M$ for all $x,y$. Then
--
--   $$\left\|\sum_i \chi_i(x)\,\bigl(S_i(x)-x\bigr) - \sum_i \chi_i(y)\,\bigl(S_i(y)-y\bigr)\right\| \le \Bigl(\sum_i (2L+M)\Bigr)\,\|x-y\|.$$
--
--   The content is a decomposition in which **every multiplied factor is bounded**. Adding and subtracting $\chi_i(y)(S_i(x)-x)$ gives the exact identity
--
--   $$\chi_i(x)(S_i(x)-x) - \chi_i(y)(S_i(y)-y) = (\chi_i(x)-\chi_i(y))(S_i(x)-x) + \chi_i(y)\bigl[(S_i(x)-x)-(S_i(y)-y)\bigr],$$
--
--   whose right-hand side is bounded by $\|x-y\|\cdot M + L\cdot 2\|x-y\| = (2L+M)\|x-y\|$: the first product uses that $\chi_i$ is $1$-Lipschitz and $\|S_i(x)-x\|\le M$, and the second uses $\|\chi_i(y)\|\le L$ together with
--
--   $$\|(S_i(x)-x)-(S_i(y)-y)\| = \|\bigl(S_i(x)-S_i(y)\bigr)-(x-y)\| \le 2\|x-y\|.$$
--
--   **The constant is $2L+M$ and the factor $2$ is essential.** The hypotheses say $S_i$ is $1$-Lipschitz, not that the displacement $d_i(v)=S_i(v)-v$ is $1$-Lipschitz, and it is not: $d_i$ is $2$-Lipschitz, with the constant $2$ attained. A bound with $L+M$ would require the false assertion $\|d_i(x)-d_i(y)\|\le\|x-y\|$. (Indeed the sibling statement with constant $L+M$ is *false*: for $n=1$, $L=1$, $M=1/2$, $S v=(s v_0,v_1,v_2)$ with $s t=-t$ on $|t|\le 1/4$ and $s t=t\mp 1/2$ outside, and $\chi(v)=\mathrm{clamp}(1-v_0)$, all hypotheses hold globally yet at $x=0$, $y=(1/8,0,0)$ the two sides are $7/32$ and $3/16$.) The outer step is subadditivity of the supremum norm over a finite sum.
-- source:
--   Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension. That leaf requires an ambient isotopy acting as a prescribed positive similarity on each round circle and the identity near all the others. Writing that ambient map as $F(x)=x+E(x)$ with $E(x)=\sum_i \chi_i(x)(S_i(x)-x)$, and taking the cutoffs from Thm_BookSixth_continuous_cutoff (theorem id faf7628a-1f49-4817-ba2b-dd2f26b3689b) on the disjoint open neighbourhoods supplied by BookSixth.pairwise_disjoint_open_neighbourhoods (theorem id 7fd98b02-98b1-425a-82fb-6b515df86aeb, Proved) and compactness from BookSixth.round_circle_is_compact (theorem id 447ecc36-9c38-481b-a4f5-9bc76f5c54a6, Proved), this bound is what makes $F$ invertible: BookSixth.small_displacement_is_homeomorph (theorem id 5f342cbf-e04b-4e47-b598-dafa8fe75f19, Proved) applies exactly when the displacement constant is below $1$, arranged by subdividing the path in time. This statement CORRECTS BookSixth.bump_perturbation_lipschitz (theorem id 010c4541-a676-4193-a55d-91cea9f7aab8), which claimed the constant $L+M$ and is false; the $2$ in $2L+M$ comes from the fact that a $1$-Lipschitz map has a $2$-Lipschitz displacement. Mathlib ingredients at c5ea0035: triangle inequality `norm_add_le` and `norm_sub_le` (Mathlib/Analysis/Normed/Group/Basic.lean:97 and :155), `norm_smul` (Mathlib/Analysis/Normed/MulAction.lean:98), finite-sum subadditivity `norm_sum_le` (Mathlib/Analysis/Normed/Group/Basic.lean:828), `dist_triangle` (Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:211), and `LipschitzWith.dist_le_mul` (Mathlib/Topology/MetricSpace/Lipschitz.lean:50, from `lipschitzWith_iff_dist_le_mul` at :45).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_lipschitz_v2 (n : ℕ) (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i)) (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i)) (hSiy : ∀ i y, ‖S i y - y‖ ≤ M) : ∀ x y : Space3, ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ (∑ i : Fin n, (2 * L + M)) * ‖x - y‖ := by sorry
