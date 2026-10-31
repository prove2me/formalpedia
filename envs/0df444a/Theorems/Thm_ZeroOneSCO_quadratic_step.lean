-- Prove2me | Theorems.Thm_ZeroOneSCO_quadratic_step
-- name    : ZeroOneSCO.quadratic_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:16.395503+00:00
-- url     : https://prove2.me/theorems/86967b1a-bcb1-41c4-b246-57cd85ea5a0a
-- title:
--   The quadratic one-step estimate, last display of p.22 (corrected: $0<\tau<\tau_*$)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $x^*$ be a $\tau$-stationary point with multiplier $W^*$ and $0<\tau<\tau_*$, suppose Assumption 2 holds, let $\rho>0$, and suppose $\varphi(\cdot;\mathcal V_*)$ and $G_{mn}$, $(m,n)\in\mathcal V_*$, are strongly semismooth at $w^*$. Then there are $\eta>0$ and $C$ such that for every $w$ with $\|w-w^*\|<\eta$, every $T\in\mathbb T(\Lambda;s)$, every $H\in\partial\varphi(w;U_T)$, every $\mu$ with $0\le\mu\le\rho\|F(w;U_T)\|$ and every solution $d$ of $\nabla F_\mu(w;U_T)\,d=-F(w;U_T)$,
--   $$
--   \|w+d-w^*\|\le C\|w-w^*\|^2.
--   $$
--   This is the quadratic counterpart of the estimate (85), with one constant for all selections.
--
--   Differences from the source:
--   - generalization: the iterates w^ℓ of Algorithm 1 near w*, with T_ℓ, H^ℓ, µ_ℓ → all w near w*, all T ∈ 𝕋(Λ; s), all H ∈ ∂ϕ(w; U_T), all 0 ≤ µ ≤ ρ‖F(w; U_T)‖; reason: the page's claim is the instance w = w^ℓ, T = T_ℓ, H = H^ℓ, µ = µ_ℓ, since µ_ℓ ≤ ρ‖F(w^ℓ; U_{T_ℓ})‖ by (79) and µ_ℓ ≥ 0; the proof on the page is uniform in these
--   - correction: no bound on τ in Theorem 5, whose proof contains this display → 0 < τ < τ*; reason: false at τ = τ*: with (M,N,K,s) = (1,2,1,1), Ω = ℝ, f(x) = x²/2 − x, G(x) = (x, 1), τ = 1, w* = (0; 1, 0), γ = 1, every printed assumption holds and τ* = 1 = τ, yet from w⁰ = (0; 1+ε, 0) the set T₀ = {2} gives w¹ = (1; 0, 1/µ₀), at distance ≥ 1 from w*, for every ε > 0
--   - reading: τ* := (Z*)↓_s / max_{n∈Γ₀*} ‖W*_{:n}‖, undefined when ‖Z*‖₀⁺ < s or W*_{:Γ₀*} = 0 → BelowTauStar: if ‖Z*‖₀⁺ = s then τ‖W*_{:n}‖ < (Z*)↓_s for all n ∈ Γ₀*, which is τ < τ* with τ* = +∞ in the undefined cases; reason: Theorem 3 allows any τ > 0 when ‖Z*‖₀⁺ < s, and Lemma 2's proof treats that case; this is the stronger reading, and it has no division
--   - reading: "ϕ(·;V)" in the second sentence of Theorem 5 → ϕ(·; V*); reason: as in Lemma 3; it is the weaker hypothesis
--   - encoding: G_mn strongly semismooth at w* → x ↦ G_mn(x) strongly semismooth at x*; reason: G_mn depends on x only
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
--   - encoding: ∇F_µ(w; V) and H = [P Q 0] in the block order of (69) → newtonMat on the index type Fin K ⊕ (Fin M × Fin N); reason: the same matrix up to one simultaneous permutation of rows and columns; the block 0 of H is automatic since ϕ(·; V) ignores W outside V
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, last display of p.22

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

namespace ZeroOneSCO

/-- The quadratic step, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, last display of p.22: under the
hypotheses of `eq_85` and strong semismoothness of `ϕ(·; V*)` and of `G_mn`, `(m,n) ∈ V*`, the Newton
step `d` of `eq_85` satisfies `‖w + d − w*‖ = O(‖w − w*‖²)`, with one constant for all selections.

**Formalization Note.** The step is any solution of the system, which `eq_85` shows to be unique. -/
theorem quadratic_step {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hτs : BelowTauStar G s τ xs Ws)
    (hA2 : Assumption2 f G Ω τ xs Ws)
    (hφ : StronglySemismoothAt11 (fun w : Wsp K M N => phi f G Ω τ w (Vstar (G xs))) (pack xs Ws))
    (hGs : ∀ p ∈ Vstar (G xs), StronglySemismoothAt11 (fun x => G x p.1 p.2) xs) :
    ∃ η > 0, ∃ C : ℝ, ∀ w : Wsp K M N, ‖w - pack xs Ws‖ < η → ∀ T ∈ TSet (Lam G τ w) s,
      ∀ H ∈ NonsmoothNewton.Shared.clarkeJac (fun v => phi f G Ω τ v (U T (Lam G τ w))) w,
      ∀ μ, 0 ≤ μ → μ ≤ ρ * ‖Fmap f G Ω τ w (U T (Lam G τ w))‖ →
      ∀ d : Wsp K M N, applyMat (newtonMat G μ w (U T (Lam G τ w)) H) d =
          -Fmap f G Ω τ w (U T (Lam G τ w)) →
        ‖w + d - pack xs Ws‖ ≤ C * ‖w - pack xs Ws‖ ^ 2 := by sorry

end ZeroOneSCO
