-- Prove2me | Theorems.Thm_ZeroOneSCO_lemma_4
-- name    : ZeroOneSCO.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:38.699876+00:00
-- url     : https://prove2.me/theorems/26989ef4-6a00-4e37-a71d-550924f8a93e
-- title:
--   Lemma 4: uniform regularity of $\nabla F_\mu(w;\mathcal V)$ (corrected: only $\mathcal V$ carrying $W^*$)
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $x^*$ be a $\tau$-stationary point with multiplier $W^*$, $\tau>0$, and suppose Assumption 2 holds. Then there are $\mu_*>0$ and a neighbourhood $\mathbb N^*$ of $w^*$ such that, for every $\mu_1<\mu_*$, there is a constant $C$ with the following property: for all $\mu\in[0,\mu_1]$, all $\mathcal V\subseteq\mathcal V_*$ with $W^*_{\overline{\mathcal V}}=0$, all $w\in\mathbb N^*$ and all $H\in\partial\varphi(w;\mathcal V)$, the matrix
--   $$
--   \nabla F_\mu(w;\mathcal V)=\begin{bmatrix}P&Q&0\\ \nabla_{\mathcal V}G(x)^\top&-\mu I_{|\mathcal V|}&0\\ 0&0&I_{|\overline{\mathcal V}|}\end{bmatrix}
--   $$
--   is nonsingular, with $\|(\nabla F_\mu(w;\mathcal V))^{-1}\|\le C$ and $\|\nabla F_\mu(w;\mathcal V)\|\le C$.
--
--   This uniform bound is what controls the Newton step over all possible selections of the index set.
--
--   Differences from the source:
--   - correction: V ⊆ V* → V ⊆ V* with W*_{V̄} = 0; reason: false otherwise: with (M,N,K,s) = (1,2,2,1), Ω = [0,∞) × ℝ, f(x) = −x₁ + (2/3)sgn(x₁)|x₁|^{3/2} − 2x₂ + x₂²/2, G(x) = (x₁ + x₂, 1), w* = (0, 0; 2, 0), 0 < τ < 1/2, ϕ(·; ∅) is not locally Lipschitz at w*, so F(·; ∅) is not semismooth and ‖∇F_µ(w; ∅)‖ is unbounded near w*. Lemma 2 shows that every U_T near w* satisfies the added condition
--   - reading: "bounded for any H and any w ∈ N*" → one C for all µ ≤ µ₁ < µ*, all admissible V, all w ∈ N*, all H; reason: this is what the proof gives and what Theorem 5 uses, and it implies the bound for each fixed µ
--   - encoding: operator norms ‖(∇F_µ)⁻¹‖ and ‖∇F_µ‖ → ‖v‖ ≤ C‖Av‖ and ‖Av‖ ≤ C‖v‖ for all v; reason: the same bounds for the Euclidean operator norm; the first with det ≠ 0 is the bound on the inverse
--   - reading: the lemma's sentence names only Assumption 2 → IsTauStationary and 0 < τ are hypotheses; reason: the preamble of §5.3 fixes a τ-stationary point
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: ∇F_µ(w; V) and H = [P Q 0] in the block order of (69) → newtonMat on the index type Fin K ⊕ (Fin M × Fin N); reason: the same matrix up to one simultaneous permutation of rows and columns; the block 0 of H is automatic since ϕ(·; V) ignores W outside V
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Lemma 4, p.20

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

open Filter Topology

namespace ZeroOneSCO

/-- Lemma 4, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.20, corrected: under Assumption 2 at a
`τ`-stationary point there are `µ* > 0` and a neighbourhood `N*` of `w*` such that `∇F_µ(w; V)` is
nonsingular for `µ ∈ [0, µ*)`, `V ⊆ V*` with `W*_{V̄} = 0`, `w ∈ N*` and `H ∈ ∂ϕ(w; V)`, and both
`‖(∇F_µ(w; V))⁻¹‖` and `‖∇F_µ(w; V)‖` are bounded.

**Formalization Note.** The page says "`V ⊆ V*`"; `W*_{V̄} = 0` is added because the bounds fail
without it. The bound is one `C` for all `µ ≤ µ₁ < µ*`, all admissible `V`, `w`, `H`, as the proof of
Theorem 5 uses it. The two norm bounds are the inequalities `‖v‖ ≤ C‖Av‖` and `‖Av‖ ≤ C‖v‖`, which say
`‖A⁻¹‖ ≤ C` and `‖A‖ ≤ C` for the Euclidean operator norm. -/
theorem lemma_4 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (τ : ℝ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hA2 : Assumption2 f G Ω τ xs Ws) :
    ∃ μs > 0, ∃ Nst ∈ 𝓝 (pack xs Ws : Wsp K M N), ∀ μ₁ < μs, ∃ C : ℝ,
      ∀ μ, 0 ≤ μ → μ ≤ μ₁ → ∀ V ⊆ Vstar (G xs), (∀ p, p ∉ V → Ws p.1 p.2 = 0) →
      ∀ w ∈ Nst, ∀ H ∈ NonsmoothNewton.Shared.clarkeJac (fun v => phi f G Ω τ v V) w,
        IsUnit (newtonMat G μ w V H).det ∧
        ∀ v : Wsp K M N, ‖v‖ ≤ C * ‖applyMat (newtonMat G μ w V H) v‖ ∧
          ‖applyMat (newtonMat G μ w V H) v‖ ≤ C * ‖v‖ := by sorry

end ZeroOneSCO
