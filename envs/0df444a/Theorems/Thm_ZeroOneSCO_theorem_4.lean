-- Prove2me | Theorems.Thm_ZeroOneSCO_theorem_4
-- name    : ZeroOneSCO.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:15.867386+00:00
-- url     : https://prove2.me/theorems/77f99ef8-5bf4-44ed-bba7-7d5df179df8a
-- title:
--   Theorem 4 ($\tau$-stationary equations)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   For $\tau>0$, $x^*\in\mathbb R^K$ and $W^*\in\mathbb R^{M\times N}$, write $Z^*:=G(x^*)$, $\Lambda^*:=Z^*+\tau W^*$ and $w^*:=(x^*;\mathrm{vec}(W^*))$. The pair $(x^*,W^*)$ satisfies the $\tau$-stationarity conditions (58) if and only if
--   $$
--   \mathbb T(\Lambda^*;s)\ni\Gamma_0^*,\qquad U_{\Gamma_0^*}=\mathcal V_*,\qquad F(w^*;\mathcal V_*)=0.
--   $$
--   The theorem turns stationarity, a condition on two projections, into a system of equations over the index set $\mathcal V_*$, to which a Newton method can be applied.
--
--   Differences from the source:
--   - generalization: x* is τ-stationary if and only if there is a W* with (71) → for each W*, (x*, W*) satisfies (58) if and only if (71) holds; reason: taking ∃ W* on both sides gives the printed statement; the proof on the page works for each W*
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Theorem 4, (71), p.18

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

namespace ZeroOneSCO

/-- Theorem 4 (`τ`-stationary equations), Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, (71), p.18: for
`τ > 0`, `(x*, W*)` satisfies (58) if and only if `𝕋(Λ*; s) ∋ Γ₀*`, `U_{Γ₀*} = V*` and
`F(w*; V*) = 0`, with `Z* = G(x*)`, `Λ* = Z* + τW*` and `w* = (x*; vec(W*))`.

**Formalization Note.** Stated for each `W*`, which gives the page's "`x*` is `τ`-stationary if and only
if there is a `W*`" by taking `∃ W*` on both sides. -/
theorem theorem_4 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (τ : ℝ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N) :
    IsTauStationary f G Ω s τ xs Ws ↔
      gammaZero (G xs) ∈ TSet (Lam G τ (pack xs Ws)) s ∧
      U (gammaZero (G xs)) (Lam G τ (pack xs Ws)) = Vstar (G xs) ∧
      Fmap f G Ω τ (pack xs Ws) (Vstar (G xs)) = 0 := by sorry

end ZeroOneSCO
