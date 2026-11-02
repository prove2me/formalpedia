-- Prove2me | Theorems.Thm_WiretapFeedback_logN_le_negLog_beta_codeLaws
-- name    : WiretapFeedback.logN_le_negLog_beta_codeLaws
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:02:33.723994+00:00
-- url     : https://prove2.me/theorems/9d37c73b-0110-4369-af7b-05286ef2a56a
-- title:
--   Proof of Theorem 6, first display — $\log N\le-\log\beta_{\epsilon+\delta+\eta}(P_{M\hat MZ^n\mathbf F},Q_{M\hat MZ^n\mathbf F})+2\log\frac1\eta$
-- statement:
--   Let $0\le\epsilon,\delta$ with $\epsilon+\delta<1$, and let $V(y,z|x)=V_2(z|x)V_1(y|z)$ be a degraded-form channel. Given an $(N,n,\epsilon,\delta)$ wiretap code for $W$, let $P_{M\hat MZ^n\mathbf F}$ be its induced law over $W$ and $Q_{M\hat MZ^n\mathbf F}$ its induced law over $V$, both with $M\sim\mathrm{unif}\{1,\dots,N\}$. Then for every $0<\eta<1-\epsilon-\delta$,
--   $$
--   \log N\le-\log\beta_{\epsilon+\delta+\eta}\bigl(P_{M\hat MZ^n\mathbf F},Q_{M\hat MZ^n\mathbf F}\bigr)+2\log\frac1\eta .
--   $$
--
--   In the paper this follows from Lemma 7 and Theorem 5 with $K=M$, $\hat K=\hat M$, $Z=(Z^n,\mathbf F)$.
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
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, pp.3–4, proof of Theorem 6, first display

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_testBeta
import Definitions.Def_WiretapFeedback_IsWiretapCode

namespace WiretapFeedback

/-- **Proof of Theorem 6, first display** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, pp. 3–4).
Given an `(N, n, ϵ, δ)` wiretap code for `W`, with `0 ≤ ϵ, δ`, `ϵ + δ < 1`, let
`P_{M M̂ Zⁿ 𝐅}` be its induced law for `M ∼ unif{1, …, N}` and `Q_{M M̂ Zⁿ 𝐅}` the law
"on `(M, M̂, Zⁿ, 𝐅)` when the underlying channel is `V`", where `V(y, z|x) = V₂(z|x) V₁(y|z)`.
Then for every `0 < η < 1 − ϵ − δ`, "by Lemma 7 and Theorem 5 we get
`log N ≤ −log β_{ϵ+δ+η}(P_{M M̂ Zⁿ 𝐅}, Q_{M M̂ Zⁿ 𝐅}) + 2 log (1/η)`."

**Formalization Note** Base-2 logarithms, `−log β` as `negLog2` in `EReal`; both laws use the
uniform message `PMF.uniformOfFintype (Fin N)`. -/
theorem logN_le_negLog_beta_codeLaws {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ} [NeZero N]
    (W V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1)
    (c : WiretapCode X Y N n) (hc : IsWiretapCode W c ε δ) (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 N : ℝ) : EReal) ≤
      negLog2 (testBeta (ε + δ + η) (c.law (PMF.uniformOfFintype (Fin N)) W)
          (c.law (PMF.uniformOfFintype (Fin N)) V)) +
        ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by sorry

end WiretapFeedback
