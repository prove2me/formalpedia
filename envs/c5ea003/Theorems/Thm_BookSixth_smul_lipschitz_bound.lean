-- Prove2me | Theorems.Thm_BookSixth_smul_lipschitz_bound
-- name    : BookSixth.smul_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T09:26:32.963962+00:00
-- url     : https://prove2.me/theorems/d456c9e2-d3f5-4012-a5c3-a2617780aad6
-- title:
--   A scalar times a small bounded vector function is Lipschitz, in displacement coordinates
-- statement:
--   Let $X$ be a normed space, let $\chi : X \to \mathbb{R}$ be scalar-valued and let $D : X \to X$. Suppose $\chi$ is Lipschitz in the multiplicative sense $|\chi(x)-\chi(y)| \le c\,\|x-y\|$, that $|\chi(x)| \le C$ everywhere, that $D$ is bounded by $M$, and that $D$ is Lipschitz with constant $L$, in the sense $\|D(x)-D(y)\| \le L\,\|x-y\|$. Then the pointwise product
--
--   $$\bigl\| \chi(x)\,D(x) - \chi(y)\,D(y) \bigr\| \le \bigl( c\,M + C\,L \bigr)\,\|x-y\|$$
--
--   is itself Lipschitz, with constant $cM+CL$.
--
--   The reason is the algebraic identity
--
--   $$\chi(x)D(x) - \chi(y)D(y) = \bigl(\chi(x)-\chi(y)\bigr) D(x) + \chi(y)\bigl(D(x)-D(y)\bigr),$$
--
--   after which the triangle inequality and the product rule for absolute values apply. The first term is controlled by $\|\chi(x)-\chi(y)\|\,\|D(x)\| \le c\,\|x-y\|\,M$ and the second by $|\chi(y)|\,\|D(x)-D(y)\| \le C\,L\,\|x-y\|$. No sign hypotheses on $c$, $M$, $C$, $L$ are needed, because they follow from the other hypotheses: $0 \le \|D(x)\| \le M$ and $0 \le |\chi(x)| \le C$ give $0 \le M$ and $0 \le C$, and the two difference hypotheses at two distinct points give $0 \le c$ and $0 \le L$.
--
--   The point of the statement is the ORDER OF THE CONSTANTS. The bound is a sum of a product of the cutoff's Lipschitz constant with the size of $D$, and a product of the cutoff's VALUE with the Lipschitz constant of $D$. Consequently the quantity that multiplies the potentially large cutoff constant is $\sup\|D\|$, the distance the vector field actually moved, rather than the cutoff value itself. In the ambient-isotopy application of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, the patch is
--
--   $$F(x) = x + \sum_i \chi_i(x)\,\bigl(S_i(x) - x\bigr),$$
--
--   where $S_i$ is the similarity that circle $i$ is required to follow, each $\chi_i$ equals $1$ on a neighbourhood of circle $i$ and $0$ near every other circle, and the patch is anisotropic away from the circles, which is harmless because only the on-circle images must stay round. Writing $D = S_i - \mathrm{id}$, the small quantity is $\sup\|D\|$, which tends to $0$ when the similarity approaches the identity. For the cutoff $f = \min 1 \bigl(\operatorname{dist}(x, K^{\mathsf c})/\delta\bigr)$ used in that application, the value bound is exactly $1$ while the sharpness is $1/\delta$, with $\delta$ the fixed positive gap of the configuration; hence $cM + CL = M/\delta + L$ tends to $0$ under subdivision of the motion in time, and the cutoff constant stays fixed and arbitrarily large. One caveat is implicit in the statement: the bound on $D$ is a global one, whereas the displacement of a global similarity is unbounded, so the displacement field must first be made compactly supported.
-- source:
--   Analytic core of the roundness-preserving ambient motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The definitions (Space3, RoundCircle, IsUnlink) are from the definition module `Definitions.Def_BookSixth`. The child is required because the two Proved catalogue lemmas BookSixth.bump_perturbation_lipschitz_v2 (00c3e7a7-f202-4293-aafe-919f3115ddd3) and BookSixth.bump_perturbation_is_homeomorph_v2 (24b19980-6e94-419a-9d06-7dfe31dd0562) bound the CUTOFF VALUE, via a hypothesis of the form `hchiL : ∀ i x, ‖chi i x‖ ≤ L` together with `hchi : ∀ i, LipschitzWith 1 (chi i)`. Because the cutoff must be equal to 1 on the moving circle, that forces L ≥ 1, so the criteria `L + M < 1` and `n * (2 * L + q) < 1` are FALSE in every application, and the 1-Lipschitz hypothesis forbids exactly the sharp cutoffs the construction needs. Restating the same estimate in displacement coordinates, with D = S - id, removes the obstruction because the small quantity is then the distance the similarity moved.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.smul_lipschitz_bound {c M C L : ℝ}
    (chi : Space3 → ℝ) (D : Space3 → Space3)
    (hchi : ∀ x y : Space3, |chi x - chi y| ≤ c * ‖x - y‖)
    (hchiC : ∀ x : Space3, |chi x| ≤ C)
    (hDM : ∀ x : Space3, ‖D x‖ ≤ M)
    (hD : ∀ x y : Space3, ‖D x - D y‖ ≤ L * ‖x - y‖) :
    ∀ x y : Space3, ‖chi x • D x - chi y • D y‖ ≤ (c * M + C * L) * ‖x - y‖ := by sorry
