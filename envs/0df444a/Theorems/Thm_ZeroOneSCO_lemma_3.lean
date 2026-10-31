-- Prove2me | Theorems.Thm_ZeroOneSCO_lemma_3
-- name    : ZeroOneSCO.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:15.129453+00:00
-- url     : https://prove2.me/theorems/c7dd5fd9-9c87-4a41-a84a-1570534894f1
-- title:
--   Lemma 3: semismoothness of $F(\cdot;\mathcal V)$ (corrected: only $\mathcal V$ carrying $W^*$)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $w^*$ be a $\tau$-stationary point with $0<\tau<\tau_*$, and let $\mathcal V\subseteq\mathcal V_*$ with $W^*_{\overline{\mathcal V}}=0$. Then:
--
--   1. if $\varphi(\cdot;\mathcal V_*)$ is semismooth at $w^*$, so is $F(\cdot;\mathcal V)$;
--   2. if $\varphi(\cdot;\mathcal V_*)$ and $G_{mn}$, $(m,n)\in\mathcal V_*$, are strongly semismooth at $w^*$, so is $F(\cdot;\mathcal V)$.
--
--   This transfers the regularity of the single map $\varphi(\cdot;\mathcal V_*)$ to all the systems the algorithm can select.
--
--   Differences from the source:
--   - correction: any V ⊆ V* → V ⊆ V* with W*_{V̄} = 0; reason: false otherwise: with (M,N,K,s) = (1,2,2,1), Ω = [0,∞) × ℝ, f(x) = −x₁ + (2/3)sgn(x₁)|x₁|^{3/2} − 2x₂ + x₂²/2, G(x) = (x₁ + x₂, 1), w* = (0, 0; 2, 0), 0 < τ < 1/2, ϕ(·; ∅) is not locally Lipschitz at w*, so F(·; ∅) is not semismooth and ‖∇F_µ(w; ∅)‖ is unbounded near w*. Lemma 2 shows that every U_T near w* satisfies the added condition
--   - reading: τ* := (Z*)↓_s / max_{n∈Γ₀*} ‖W*_{:n}‖, undefined when ‖Z*‖₀⁺ < s or W*_{:Γ₀*} = 0 → BelowTauStar: if ‖Z*‖₀⁺ = s then τ‖W*_{:n}‖ < (Z*)↓_s for all n ∈ Γ₀*, which is τ < τ* with τ* = +∞ in the undefined cases; reason: Theorem 3 allows any τ > 0 when ‖Z*‖₀⁺ < s, and Lemma 2's proof treats that case; this is the stronger reading, and it has no division
--   - encoding: G_mn strongly semismooth at w* → x ↦ G_mn(x) strongly semismooth at x*; reason: G_mn depends on x only
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Lemma 3, p.20

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

namespace ZeroOneSCO

/-- Lemma 3, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.20, corrected: at a `τ`-stationary point with
`0 < τ < τ*`, for `V ⊆ V*` with `W*_{V̄} = 0`, semismoothness of `ϕ(·; V*)` at `w*` gives semismoothness
of `F(·; V)` at `w*`, and strong semismoothness of `ϕ(·; V*)` and of `G_mn`, `(m,n) ∈ V*`, gives strong
semismoothness of `F(·; V)` at `w*`.

**Formalization Note.** The page says "any `V ⊆ V*`"; `W*_{V̄} = 0` is added because the statement is
false without it (`ϕ(·; V)` need not be locally Lipschitz at `w*`). Lemma 2 shows that every `U_T` near
`w*` qualifies. `G_mn` is strongly semismooth as a function of `x`, at `x*`. -/
theorem lemma_3 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (τ : ℝ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hτs : BelowTauStar G s τ xs Ws)
    (V : Finset (Fin M × Fin N)) (hV : V ⊆ Vstar (G xs)) (hWV : ∀ p, p ∉ V → Ws p.1 p.2 = 0) :
    (SemismoothAt10 (fun w : Wsp K M N => phi f G Ω τ w (Vstar (G xs))) (pack xs Ws) →
      SemismoothAt10 (fun w : Wsp K M N => Fmap f G Ω τ w V) (pack xs Ws)) ∧
    (StronglySemismoothAt11 (fun w : Wsp K M N => phi f G Ω τ w (Vstar (G xs))) (pack xs Ws) →
      (∀ p ∈ Vstar (G xs), StronglySemismoothAt11 (fun x => G x p.1 p.2) xs) →
      StronglySemismoothAt11 (fun w : Wsp K M N => Fmap f G Ω τ w V) (pack xs Ws)) := by sorry

end ZeroOneSCO
