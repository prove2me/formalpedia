-- Prove2me | Theorems.Thm_ZeroOneSCO_theorem_5
-- name    : ZeroOneSCO.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:57.692732+00:00
-- url     : https://prove2.me/theorems/44f864e0-007a-47cf-8f44-13c7d2463fc4
-- title:
--   Theorem 5 (Local convergence rate): SNSCO takes full Newton steps and converges superlinearly or quadratically (corrected: $0<\tau<\tau_*$)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $x^*$ be a $\tau$-stationary point of (SCO) with multiplier $W^*$ and $0<\tau<\tau_*$, let $w^*:=(x^*;\mathrm{vec}(W^*))$, suppose Assumption 2 holds, and let $\gamma\ge|\Gamma_0^*|/s$. Let $\rho,\underline\mu,\gamma,\nu,\pi$ be the parameters of Algorithm 1.
--
--   1. There is $\eta>0$ such that every run of Algorithm 1 with $\|w^0-w^*\|<\eta$ takes full Newton steps (at every $\ell$ the direction $d^\ell$ solves the Newton system (78) and $t_\ell=0$, so $w^{\ell+1}=w^\ell+d^\ell$), converges to $w^*$, and satisfies
--   $$
--   \|w^{\ell+1}-w^*\|=o(\|w^\ell-w^*\|).
--   $$
--   2. If moreover $\varphi(\cdot;\mathcal V_*)$ and $G_{mn}$, $(m,n)\in\mathcal V_*$, are strongly semismooth at $w^*$, then there are $\eta>0$ and $C$ such that every run with $\|w^0-w^*\|<\eta$ takes full Newton steps in the same sense, converges to $w^*$, and satisfies
--   $$
--   \|w^{\ell+1}-w^*\|\le C\|w^\ell-w^*\|^2.
--   $$
--
--   The statement covers every selection of $T_\ell\in\mathbb T(\Lambda^\ell;s)$ and $H^\ell\in\partial\varphi(w^\ell;U_{T_\ell})$. Each step solves a different system $F(\cdot;U_{T_\ell})=0$, so the theorem is a Newton convergence result with a varying index set.
--
--   **Formalization Note** The numbers $\eta$ and $C$ depend on the instance and on the parameters and come before the run.
--
--   Differences from the source:
--   - correction: no bound on τ in the sentence of Theorem 5 → 0 < τ < τ*; reason: false at τ = τ*: with (M,N,K,s) = (1,2,1,1), Ω = ℝ, f(x) = x²/2 − x, G(x) = (x, 1), τ = 1, w* = (0; 1, 0), γ = 1, every printed assumption holds and τ* = 1 = τ, yet from w⁰ = (0; 1+ε, 0) the set T₀ = {2} gives w¹ = (1; 0, 1/µ₀), at distance ≥ 1 from w*, for every ε > 0. It is the hypothesis Lemma 2 states
--   - reading: τ* := (Z*)↓_s / max_{n∈Γ₀*} ‖W*_{:n}‖, undefined when ‖Z*‖₀⁺ < s or W*_{:Γ₀*} = 0 → BelowTauStar: if ‖Z*‖₀⁺ = s then τ‖W*_{:n}‖ < (Z*)↓_s for all n ∈ Γ₀*, which is τ < τ* with τ* = +∞ in the undefined cases; reason: Theorem 3 allows any τ > 0 when ‖Z*‖₀⁺ < s, and Lemma 2's proof treats that case; this is the stronger reading, and it has no division
--   - reading: "ϕ(·;V)" unstarred in the second sentence → ϕ(·; V*); reason: as in Lemma 3; it is the weaker hypothesis and so the stronger theorem
--   - reading: Algorithm 1 line 3 with tol > 0 and maxIt → a run with no stopping test; reason: a stopped run is a prefix of such a sequence, and a rate is a statement about a sequence
--   - reading: "Algorithm 1 admits full Newton steps" → at every ℓ, d^ℓ solves (78) and t_ℓ = 0; reason: the proof on p.22 shows (78) solvable and π^{t_ℓ} = 1, "namely, w^{ℓ+1} = w^ℓ + d^ℓ", and Remark 4 iii (p.20) reads (80) with π^{t_ℓ} = 1
--   - encoding: G_mn strongly semismooth at w* → x ↦ G_mn(x) strongly semismooth at x*; reason: G_mn depends on x only
--   - encoding: γ ≥ |Γ₀*|/s → |Γ₀*| ≤ γ s; reason: s > 0
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
--   - encoding: ∇F_µ(w; V) and H = [P Q 0] in the block order of (69) → newtonMat on the index type Fin K ⊕ (Fin M × Fin N); reason: the same matrix up to one simultaneous permutation of rows and columns; the block 0 of H is automatic since ϕ(·; V) ignores W outside V
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Theorem 5, p.21

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations
import Definitions.Def_ZeroOneSCO_Algorithm

open Filter Topology

namespace ZeroOneSCO

/-- Theorem 5 (Local convergence rate), Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.21, corrected with
`0 < τ < τ*`: at a `τ`-stationary point, under Assumption 2 and `γ ≥ |Γ₀*|/s`, in a neighbourhood of `w*`
Algorithm 1 admits full Newton steps and converges to `w*` superlinearly; if further `ϕ(·; V*)` and
`G_mn`, `(m,n) ∈ V*`, are strongly semismooth at `w*`, the convergence is quadratic.

**Formalization Note.** The conclusion covers every run started in the neighbourhood, for every
selection `T_ℓ`, `H^ℓ`. "Admits full Newton steps" is read as on p.22: at every step `d^ℓ` solves the
Newton system (78) and the step size of (80) is `π^{t_ℓ} = 1`, i.e. `t_ℓ = 0`. `η`, and `C` in the quadratic clause, come before the run. The hypothesis
`BelowTauStar` is Lemma 2's `τ < τ*`, absent from the sentence of Theorem 5 and needed: the theorem
is false at `τ = τ*`. `ϕ(·; V)` in the second sentence is read as `ϕ(·; V*)`, as in Lemma 3. The bound
`γ ≥ |Γ₀*|/s` is written `|Γ₀*| ≤ γ s`. -/
theorem theorem_5 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (ρ τ μbar γ ν π : ℝ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hτs : BelowTauStar G s τ xs Ws)
    (hA2 : Assumption2 f G Ω τ xs Ws)
    (hγ : ((gammaZero (G xs)).card : ℝ) ≤ γ * s) :
    (∃ η > 0, ∀ (w : ℕ → Wsp K M N) (T : ℕ → Finset (Fin N)) (H : ℕ → Wsp K M N →L[ℝ] Pt K)
        (μ : ℕ → ℝ) (d : ℕ → Wsp K M N) (t : ℕ → ℕ),
        IsSNSCORun f G Ω s ρ τ μbar γ ν π w T H μ d t → ‖w 0 - pack xs Ws‖ < η →
        (∀ ℓ, applyMat (newtonMat G (μ ℓ) (w ℓ) (U (T ℓ) (Lam G τ (w ℓ))) (H ℓ)) (d ℓ) =
          -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))) ∧
        (∀ ℓ, t ℓ = 0) ∧ Tendsto w atTop (𝓝 (pack xs Ws)) ∧
        (fun ℓ => w (ℓ + 1) - pack xs Ws) =o[atTop] (fun ℓ => w ℓ - pack xs Ws)) ∧
    (StronglySemismoothAt11 (fun w : Wsp K M N => phi f G Ω τ w (Vstar (G xs))) (pack xs Ws) →
      (∀ p ∈ Vstar (G xs), StronglySemismoothAt11 (fun x => G x p.1 p.2) xs) →
      ∃ η > 0, ∃ C : ℝ, ∀ (w : ℕ → Wsp K M N) (T : ℕ → Finset (Fin N))
        (H : ℕ → Wsp K M N →L[ℝ] Pt K) (μ : ℕ → ℝ) (d : ℕ → Wsp K M N) (t : ℕ → ℕ),
        IsSNSCORun f G Ω s ρ τ μbar γ ν π w T H μ d t → ‖w 0 - pack xs Ws‖ < η →
        (∀ ℓ, applyMat (newtonMat G (μ ℓ) (w ℓ) (U (T ℓ) (Lam G τ (w ℓ))) (H ℓ)) (d ℓ) =
          -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))) ∧
        (∀ ℓ, t ℓ = 0) ∧ Tendsto w atTop (𝓝 (pack xs Ws)) ∧
        ∀ ℓ, ‖w (ℓ + 1) - pack xs Ws‖ ≤ C * ‖w ℓ - pack xs Ws‖ ^ 2) := by sorry

end ZeroOneSCO
