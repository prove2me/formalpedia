-- Prove2me | Theorems.Thm_YeIPA_MCP_central_step
-- name    : YeIPA.MCP.central_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:42.766629+00:00
-- url     : https://prove2.me/theorems/4d43d4b5-5c30-4afd-9343-69413d4b43e0
-- title:
--   Theorem 8.29 — the full step with $\eta=\beta/\sqrt{n+1}$, $\gamma=1-\eta$ keeps the iterate positive and in the neighborhood $\|Xs-\mu e\|\le\beta\mu$
-- statement:
--   Let $f$ be a continuous monotone map from the open orthant $\mathbb R^n_{++}$ to $\mathbb R^n$, differentiable there, and let $\psi(x,\tau)=(\tau f(x/\tau);\,-x^Tf(x/\tau))$ be the homogeneous map (8.23) on $\mathbb R^{n+1}_{++}$. Assume $\psi$ is **scaled Lipschitz** with a function $v_\psi:(0,1)\to(1,\infty)$, monotone increasing: for all $x\in\mathbb R^{n+1}_{++}$, $d\in\mathbb R^{n+1}$ and $\alpha\in(0,1)$ with $\|X^{-1}d\|_\infty\le\alpha$,
--   $$\|X(\psi(x+d)-\psi(x)-\nabla\psi(x)d)\|_1\le v_\psi(\alpha)\,d^T\nabla\psi(x)d.$$
--   Let
--   $$\beta=\frac1{3+4v_\psi(\sqrt2/2)},\qquad \eta=\frac{\beta}{\sqrt{n+1}},\qquad\gamma=1-\eta,\qquad\alpha=1.$$
--   Let $(x^k,s^k)>0$ in $\mathbb R^{n+1}\times\mathbb R^{n+1}$ satisfy $\|X^ks^k-\mu^ke\|\le\beta\mu^k$ with $\mu^k=(x^k)^Ts^k/(n+1)$ ($\|\cdot\|$ Euclidean), let $r^k=s^k-\psi(x^k)$, and let $(d_x,d_s)$ solve $d_s-\nabla\psi(x^k)d_x=-\eta r^k$ (8.42) and $X^kd_s+S^kd_x=\gamma\mu^ke-X^ks^k$ (8.43). Set $x^+=x^k+d_x$ and $s^+=s^k+d_s+\psi(x^+)-\psi(x^k)-\nabla\psi(x^k)d_x$ ((8.46)–(8.47) with $\alpha=1$). Then $\beta\le1/3$,
--   $$x^+>0,\qquad s^+=\psi(x^+)+(1-\eta)r^k>0,\qquad\text{and}\qquad\|X^+s^+-\mu^+e\|\le\beta\mu^+,\quad\mu^+=\frac{(x^+)^Ts^+}{n+1}.$$
--
--   This is the one-step invariant of the homogeneous interior-point algorithm for the monotone complementarity problem: the iterates stay in a fixed neighborhood of the central path while the residual $r^k$ and the gap $(x^k)^Ts^k$ both shrink by the factor $1-\beta/\sqrt{n+1}$ per step, which gives the $O(\sqrt n\log(1/\epsilon))$ iteration bound when $v_\psi(\sqrt2/2)$ is a constant.
--
--   **Formalization Note** All constants are the book's own ($\beta$, $\eta$, $\gamma$, $\alpha=1$); there is no $O(\cdot)$ in the statement. $\nabla\psi$ is Mathlib's `fderiv` of `psi f`; the points of $\mathbb R^{n+1}$ are $(x;\tau)$ and $(s;\kappa)$ as on p. 268. The scaled Lipschitz condition bundles the properties of $v_\psi$ ($v_\psi>1$ and nondecreasing on $(0,1)$). The standing assumptions of §8.4 (continuity and monotonicity of $f$ on $\mathbb R^n_{++}$, p. 257) and differentiability of $f$ (behind $\nabla\psi$) are explicit hypotheses. Any solution of (8.42)–(8.43) is allowed. The conclusion includes the closed form of $s^+$ and the remark $\beta\le1/3$, both part of the printed statement.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 270, Theorem 8.29

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Theorem 8.29 (Ye 1997, p. 270). Let `f` be continuous, monotone and differentiable on
`ℝⁿ₊₊` (standing assumptions of §8.4) and assume `ψ` of (8.23) is scaled Lipschitz with
`v = v_ψ`. Let `(xᵏ, sᵏ) > 0` in `ℝⁿ⁺¹` with `‖Xᵏsᵏ − μᵏe‖ ≤ βμᵏ`,
`μᵏ = (xᵏ)ᵀsᵏ/(n + 1)`, where `β = 1/(3 + 4v_ψ(√2/2))`. Let `η = β/√(n + 1)`,
`γ = 1 − η`, `α = 1`, and let `(d_x, d_s)` solve (8.42)–(8.43). Then `β ≤ 1/3`, the new
iterate satisfies `x⁺ > 0`, `s⁺ = ψ(x⁺) + (1 − η)rᵏ > 0`, and `‖X⁺s⁺ − μ⁺e‖ ≤ βμ⁺` with
`μ⁺ = (x⁺)ᵀs⁺/(n + 1)`. -/
theorem central_step {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (v : ℝ → ℝ) (hψ : ScaledLipschitz (psi f) v)
    (β η γ : ℝ) (hβ : β = 1 / (3 + 4 * v (Real.sqrt 2 / 2)))
    (hη : η = β / Real.sqrt ((n : ℝ) + 1)) (hγ : γ = 1 - η)
    (x s dx ds : Fin (n + 1) → ℝ) (hx : x ∈ posOrthant (n + 1)) (hs : s ∈ posOrthant (n + 1))
    (hnbhd : norm2 (fun i => x i * s i - mu x s) ≤ β * mu x s)
    (hdir : IsDirection f η γ x s dx ds) :
    β ≤ 1 / 3 ∧
    newX x dx 1 ∈ posOrthant (n + 1) ∧
    newS f x s dx ds 1 = psi f (newX x dx 1) + (1 - η) • residual f x s ∧
    newS f x s dx ds 1 ∈ posOrthant (n + 1) ∧
    norm2 (fun i => newX x dx 1 i * newS f x s dx ds 1 i -
        mu (newX x dx 1) (newS f x s dx ds 1)) ≤
      β * mu (newX x dx 1) (newS f x s dx ds 1) := by sorry

end YeIPA.MCP
