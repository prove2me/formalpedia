-- Prove2me | Theorems.Thm_ZeroOneSCO_lemma_2
-- name    : ZeroOneSCO.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:25.318677+00:00
-- url     : https://prove2.me/theorems/01f69d1b-5927-4afc-8cb1-fb964df3fd2f
-- title:
--   Lemma 2: identification of the active set near $w^*$
-- statement:
--   Let $f:\mathbb R^K\to\mathbb R$ and $G:\mathbb R^K\to\mathbb R^{M\times N}$ be continuously differentiable, let $\Omega\subseteq\mathbb R^K$ be nonempty, closed and convex, and let $s\ge 1$ be an integer.
--
--   Let $x^*$ be a $\tau$-stationary point with multiplier $W^*$ and $0<\tau<\tau_*$, and let $w^*:=(x^*;\mathrm{vec}(W^*))$. Then there is a neighbourhood $\mathbb N^*$ of $w^*$ such that
--   $$
--   F(w^*;U_T)=0\quad\text{and}\quad U_T\subseteq\mathcal V_*,\qquad\forall w\in\mathbb N^*,\ \forall T\in\mathbb T(\Lambda;s).
--   $$
--   Here $U_T$ is built from $\Lambda=G(x)+\tau W$ at $w$, while $F$ is evaluated at $w^*$.
--
--   So whichever index set the algorithm selects near $w^*$, the point $w^*$ solves the corresponding system, though the selected set can change from step to step.
--
--   Differences from the source:
--   - reading: τ* := (Z*)↓_s / max_{n∈Γ₀*} ‖W*_{:n}‖, undefined when ‖Z*‖₀⁺ < s or W*_{:Γ₀*} = 0 → BelowTauStar: if ‖Z*‖₀⁺ = s then τ‖W*_{:n}‖ < (Z*)↓_s for all n ∈ Γ₀*, which is τ < τ* with τ* = +∞ in the undefined cases; reason: Theorem 3 allows any τ > 0 when ‖Z*‖₀⁺ < s, and Lemma 2's proof treats that case; this is the stronger reading, and it has no division
--   - encoding: index sets 𝓜 = {1,…,M}, 𝓝 = {1,…,N}, with the column maximum of p.3 presupposing M ≥ 1 → Fin M, Fin N (0-based) with [NeZero M]; reason: Lean convention; the page takes a maximum over 𝓜, so 𝓜 is nonempty
--   - reading: s ≪ N is a given positive integer → 0 < s; reason: "≪" is informal and no proof uses it
--   - reading: (SCO) on p.3 states continuous differentiability only for G, and f is continuously differentiable on p.1 → ContDiff ℝ 1 f and ContDiff ℝ 1 of each entry G_mn, with Ω nonempty, closed and convex; reason: the standing assumptions of p.1 and p.3 carried over; Ω nonempty is implied by x* ∈ Ω
--   - encoding: Π_Ω(z), the unique minimizer of ‖z − y‖ over Ω → projOmega Ω z, chosen by Classical.epsilon; reason: Lean convention; projOmega_spec shows it is the minimizer for nonempty closed Ω, and uniqueness follows from convexity
--   - encoding: w = (x; vec(W)) and F(w; V) in the stacked block order → vectors on the index type Fin K ⊕ (Fin M × Fin N); reason: the same vectors up to one permutation of coordinates, which preserves the Euclidean norm
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, Lemma 2, (82), p.20, proof pp.29–30

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth
import Definitions.Def_ZeroOneSCO_Equations

open Filter Topology

namespace ZeroOneSCO

/-- Lemma 2, Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, (82), p.20 (proof pp.29–30): at a `τ`-stationary
point with `0 < τ < τ*` there is a neighbourhood `N*` of `w*` with `F(w*; U_T) = 0` and `U_T ⊆ V*` for
all `w ∈ N*` and all `T ∈ 𝕋(Λ; s)`, where `U_T` is built from `Λ` at `w`.

**Formalization Note.** `F` is evaluated at `w*`, and the index set comes from `w`. -/
theorem lemma_2 {K M N : ℕ} [NeZero M]
    (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (s : ℕ)
    (hf : ContDiff ℝ 1 f) (hG : ∀ m n, ContDiff ℝ 1 fun x => G x m n)
    (hΩne : Ω.Nonempty) (hΩclosed : IsClosed Ω) (hΩconv : Convex ℝ Ω) (hs : 0 < s)
    (τ : ℝ) (hτ : 0 < τ) (xs : Pt K) (Ws : Mat M N)
    (hstat : IsTauStationary f G Ω s τ xs Ws) (hτs : BelowTauStar G s τ xs Ws) :
    ∃ Nst ∈ 𝓝 (pack xs Ws : Wsp K M N), ∀ w ∈ Nst, ∀ T ∈ TSet (Lam G τ w) s,
      Fmap f G Ω τ (pack xs Ws) (U T (Lam G τ w)) = 0 ∧ U T (Lam G τ w) ⊆ Vstar (G xs) := by sorry

end ZeroOneSCO
