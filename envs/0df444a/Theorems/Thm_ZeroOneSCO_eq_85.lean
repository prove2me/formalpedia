-- Prove2me | Theorems.Thm_ZeroOneSCO_eq_85
-- name    : ZeroOneSCO.eq_85
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:22.898234+00:00
-- url     : https://prove2.me/theorems/8c070ac7-0dfb-4e31-a6fb-6b6de67ff83a
-- title:
--   Display (85): the one-step estimate with the full-step count (corrected: $0<\tau<\tau_*$)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $x^*$ be a $\tau$-stationary point with multiplier $W^*$ and $0<\tau<\tau_*$, suppose Assumption 2 holds, and let $\rho>0$. For every $\varepsilon>0$ there is $\eta>0$ such that for every $w$ with $\|w-w^*\|<\eta$, every $T\in\mathbb T(\Lambda;s)$, every $H\in\partial\varphi(w;U_T)$ and every $\mu$ with $0\le\mu\le\rho\|F(w;U_T)\|$, the system
--   $$
--   \nabla F_\mu(w;U_T)\,d=-F(w;U_T)
--   $$
--   has exactly one solution $d$, and this solution satisfies
--   $$
--   \|G(x+d_x)\|_0^+\le|\Gamma_+^*|+|\Gamma_0^*|,\qquad \|w+d-w^*\|\le\varepsilon\|w-w^*\|.
--   $$
--   This is the single step of the convergence proof: the Newton step is defined, passes the test (80) with unit step size, and reduces the distance to $w^*$ at a superlinear rate.
--
--   Differences from the source:
--   - generalization: the iterates w^ℓ of Algorithm 1 near w*, with T_ℓ, H^ℓ, µ_ℓ → all w near w*, all T ∈ 𝕋(Λ; s), all H ∈ ∂ϕ(w; U_T), all 0 ≤ µ ≤ ρ‖F(w; U_T)‖; reason: the page's claim is the instance w = w^ℓ, T = T_ℓ, H = H^ℓ, µ = µ_ℓ, since µ_ℓ ≤ ρ‖F(w^ℓ; U_{T_ℓ})‖ by (79) and µ_ℓ ≥ 0; the proof on the page is uniform in these
--   - correction: no bound on τ in Theorem 5, whose proof contains (85) → 0 < τ < τ*; reason: false at τ = τ*: with (M,N,K,s) = (1,2,1,1), Ω = ℝ, f(x) = x²/2 − x, G(x) = (x, 1), τ = 1, w* = (0; 1, 0), γ = 1, every printed assumption holds and τ* = 1 = τ, yet from w⁰ = (0; 1+ε, 0) the set T₀ = {2} gives w¹ = (1; 0, 1/µ₀), at distance ≥ 1 from w*, for every ε > 0
--   - reading: τ* := (Z*)↓_s / max_{n∈Γ₀*} ‖W*_{:n}‖, undefined when ‖Z*‖₀⁺ < s or W*_{:Γ₀*} = 0 → BelowTauStar: if ‖Z*‖₀⁺ = s then τ‖W*_{:n}‖ < (Z*)↓_s for all n ∈ Γ₀*, which is τ < τ* with τ* = +∞ in the undefined cases; reason: Theorem 3 allows any τ > 0 when ‖Z*‖₀⁺ < s, and Lemma 2's proof treats that case; this is the stronger reading, and it has no division
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
--   - encoding: ∇F_µ(w; V) and H = [P Q 0] in the block order of (69) → newtonMat on the index type Fin K ⊕ (Fin M × Fin N); reason: the same matrix up to one simultaneous permutation of rows and columns; the block 0 of H is automatic since ϕ(·; V) ignores W outside V
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, (85), p.22, with the count on p.22

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

namespace ZeroOneSCO

/-- Display (85), Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.22, with the count on the same page, in a
form uniform over the selection: near `w*`, for every `T ∈ 𝕋(Λ; s)`, `V = U_T`, `H ∈ ∂ϕ(w; V)` and
`0 ≤ µ ≤ ρ‖F(w; V)‖`, the system `∇F_µ(w; V) d = −F(w; V)` has exactly one solution `d`, this `d` satisfies
`‖G(x + d_x)‖₀⁺ ≤ |Γ₊*| + |Γ₀*|`, and `‖w + d − w*‖ ≤ ε‖w − w*‖`.

**Formalization Note.** The `o(‖w^ℓ − w*‖)` of (85) is the `∀ ε > 0, ∃ η > 0` here. -/
theorem eq_85 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hτs : BelowTauStar G s τ xs Ws)
    (hA2 : Assumption2 f G Ω τ xs Ws) :
    ∀ ε > 0, ∃ η > 0, ∀ w : Wsp K M N, ‖w - pack xs Ws‖ < η → ∀ T ∈ TSet (Lam G τ w) s,
      ∀ H ∈ NonsmoothNewton.Shared.clarkeJac (fun v => phi f G Ω τ v (U T (Lam G τ w))) w,
      ∀ μ, 0 ≤ μ → μ ≤ ρ * ‖Fmap f G Ω τ w (U T (Lam G τ w))‖ →
      ∃ d : Wsp K M N,
        (∀ d' : Wsp K M N, applyMat (newtonMat G μ w (U T (Lam G τ w)) H) d' =
          -Fmap f G Ω τ w (U T (Lam G τ w)) ↔ d' = d) ∧
        plusZero (G (xPart (w + d))) ≤ (gammaPos (G xs)).card + (gammaZero (G xs)).card ∧
        ‖w + d - pack xs Ws‖ ≤ ε * ‖w - pack xs Ws‖ := by sorry

end ZeroOneSCO
