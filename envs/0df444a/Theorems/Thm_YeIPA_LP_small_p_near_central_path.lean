-- Prove2me | Theorems.Thm_YeIPA_LP_small_p_near_central_path
-- name    : YeIPA.LP.small_p_near_central_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:34.921986+00:00
-- url     : https://prove2.me/theorems/177eb1cc-c62c-498b-8dcd-267961e49473
-- title:
--   Lemma 4.8 — if $\|p(z^k)\|$ is small then $s(z^k)>0$, $(x^k,s(z^k))$ is near the central path and the gap drops
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $n\ge1$, $b\ne0$, and let (LP) and (LD) have interior feasible points. Let $(x^k,y^k,s^k)\in\mathring{\mathcal F}$, let $\rho=\sqrt n$, $z^k=b^Ty^k$, and let $p(z^k)$, $y(z^k)$ and $s(z^k)=c-A^Ty(z^k)$ be as in the potential-reduction step (p. 121, (4.12), (4.13)). Put
--   $$\mu^k=\frac{(x^k)^Ts^k}{n}=\frac{c^Tx^k-z^k}{n},\qquad \mu=\frac{(x^k)^Ts(z^k)}{n}.$$
--   Let $\eta\in\mathbb R$. If
--   $$\|p(z^k)\|<\min\Big(\eta\sqrt{\frac{n}{n+\eta^2}},\ 1-\eta\Big)\quad(4.14),$$
--   then
--   $$s(z^k)>0,\qquad \|X^ks(z^k)-\mu e\|<\eta\mu,\qquad \mu<\Big(1-\frac{.5\eta}{\sqrt n}\Big)\mu^k\quad(4.15).$$
--
--   The lemma says that when the primal step of the potential-reduction algorithm would make little progress, the dual update $s(z^k)$ is feasible, close to the central path and reduces the duality gap, which is the second case of Theorem 4.9.
--
--   **Formalization Note** The choice $\rho=\sqrt n$ is the standing choice of §4.3 (p. 121) and is built into the statement. The standing assumptions (rank $m$, interior points, p. 63; $b\ne0$, p. 109) and $n\ge1$ are explicit hypotheses. $\mu^k$ is written $(x^k)^Ts^k/n$; its equality with $(c^Tx^k-z^k)/n$ holds by feasibility and is not part of the conclusion. As printed, $\eta$ is unrestricted (for $\eta\le0$ or $\eta\ge1$ the hypothesis (4.14) cannot hold).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 122, Lemma 4.8

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Lemma 4.8 (Ye 1997, p. 122). Under the standing assumptions (p. 63), let
`(xᵏ, yᵏ, sᵏ) ∈ F̊`, `ρ = √n` (§4.3, p. 121), `zᵏ = bᵀyᵏ`, `μᵏ = (xᵏ)ᵀsᵏ/n` and
`μ = (xᵏ)ᵀs(zᵏ)/n`. If `‖p(zᵏ)‖ < min(η√(n/(n + η²)), 1 − η)` (4.14), then
`s(zᵏ) > 0`, `‖Xᵏs(zᵏ) − μe‖ < ημ` and `μ < (1 − .5η/√n)μᵏ` (4.15). -/
theorem small_p_near_central_path {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (η : ℝ)
    (hp : norm2 (pVec A c (Real.sqrt n) x (b ⬝ᵥ y)) <
      min (η * Real.sqrt (n / (n + η ^ 2))) (1 - η)) :
    (∀ j, 0 < sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) j) ∧
      norm2 (fun j => x j * sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) j
          - x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n) <
        η * (x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n) ∧
      x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n <
        (1 - η / (2 * Real.sqrt n)) * (x ⬝ᵥ s / n) := by sorry

end YeIPA.LP
