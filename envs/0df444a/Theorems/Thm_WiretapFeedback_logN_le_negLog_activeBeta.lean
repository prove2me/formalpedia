-- Prove2me | Theorems.Thm_WiretapFeedback_logN_le_negLog_activeBeta
-- name    : WiretapFeedback.logN_le_negLog_activeBeta
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:02:58.171498+00:00
-- url     : https://prove2.me/theorems/80933ff8-6001-4edf-b274-8103d0c2eb0e
-- title:
--   Theorem 6 — finite-blocklength converse for wiretap codes with feedback
-- statement:
--   Let $0\le\epsilon,\delta$ with $\epsilon+\delta<1$. For every $(N,n,\epsilon,\delta)$ wiretap code with public feedback for the channel $W:\mathcal X\to\mathcal Y\times\mathcal Z$,
--   $$
--   \log N\le-\log\beta_{\epsilon+\delta+\eta}(W,V,n)+2\log\frac1\eta
--   $$
--   for all $0<\eta<1-\epsilon-\delta$ and all channels $V:\mathcal X\to\mathcal Y\times\mathcal Z$ such that $V(y,z|x)=V_2(z|x)V_1(y|z)$, where $\beta_{\epsilon}(W,V,n)$ is the optimal type-II error of $n$-length active hypothesis testing between $W$ and $V$.
--
--   This bound holds for every fixed blocklength $n$; combined with Theorem 4 it gives Theorem 1.
--
--   **Formalization Note** Logarithms are base 2 and $-\log\beta$ is extended-real valued.
--
--   Differences from the source:
--   - encoding: log (base fixed by ⌊2^{nR}⌋), −log β real-valued → Real.logb 2; −log β as negLog2 in EReal (+∞ at β = 0); reason: Lean convention; β = 0 is reachable and −log 0 = +∞ is the page's value
--   - encoding: an (N, n, ϵ, δ) wiretap code (N ≥ 1 implicit) → [NeZero N] and IsWiretapCode W c ϵ δ; reason: the uniform message law needs N ≥ 1
--   - encoding: a channel V with V(y,z|x) = V₂(z|x)V₁(y|z) → V with hypothesis ∀ x y z, V(y,z|x) = V₂(z|x)·V₁(y|z) for channels V₂, V₁; reason: Lean convention; the same channels
--   - encoding: (possibly randomized) encoder and feedback mappings, time index t = 1, …, n, messages {1, …, N} → deterministic maps of independent local randomness Ux, Uy of arbitrary type (paper's own representation, proof of Lemma 7), arbitrary feedback alphabet, 0-based rounds, Fin N; reason: Lean convention; the same class of codes
--   - generalization: discrete (finite) input alphabet X → any type X, with Y and Z finite; reason: neither the statement nor its proof forms a law on X or uses finiteness of X; every finite X is an instance
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, p.3, Theorem 6

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_IsWiretapCode

namespace WiretapFeedback

/-- **Theorem 6** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3). For `0 ≤ ϵ, δ`, `ϵ + δ < 1`,
given an `(N, n, ϵ, δ)`-wiretap code, we have
`log N ≤ −log β_{ϵ+δ+η}(W, V, n) + 2 log (1/η)`
for all `0 < η < 1 − ϵ − δ` and all channels `V : X → Y × Z` such that
`V(y, z|x) = V₂(z|x) V₁(y|z)`.

**Formalization Note** Base-2 logarithms; `−log β` is `negLog2` (`+∞` at `β = 0`), so the bound is
in `EReal`. `β_ϵ(W, V, n)` is `activeBeta`, the infimum over all `n`-length active hypothesis
tests with arbitrary feedback alphabet and local randomness. `V₂ : X → Z`, `V₁ : Z → Y` are
channels. -/
theorem logN_le_negLog_activeBeta {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ} [NeZero N]
    (W V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1)
    (c : WiretapCode X Y N n) (hc : IsWiretapCode W c ε δ) (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 N : ℝ) : EReal) ≤
      negLog2 (activeBeta (ε + δ + η) W V n) + ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by sorry

end WiretapFeedback
