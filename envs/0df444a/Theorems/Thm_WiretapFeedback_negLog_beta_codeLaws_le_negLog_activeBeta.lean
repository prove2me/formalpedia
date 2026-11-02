-- Prove2me | Theorems.Thm_WiretapFeedback_negLog_beta_codeLaws_le_negLog_activeBeta
-- name    : WiretapFeedback.negLog_beta_codeLaws_le_negLog_activeBeta
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:02:38.745598+00:00
-- url     : https://prove2.me/theorems/7bd61316-bac1-4faf-b052-05e6487058d8
-- title:
--   Proof of Theorem 6, second display — a wiretap code with a test is an active hypothesis test
-- statement:
--   Let a wiretap code with public feedback, a message law $\mu$, two channels $W,V:\mathcal X\to\mathcal Y\times\mathcal Z$ and $0\le\epsilon'<1$ be given, and let $P_{M\hat MZ^n\mathbf F}$ and $Q_{M\hat MZ^n\mathbf F}$ be the laws of $(M,\hat M,Z^n,\mathbf F)$ when the code is run over $W$ and over $V$. Then
--   $$
--   -\log\beta_{\epsilon'}\bigl(P_{M\hat MZ^n\mathbf F},Q_{M\hat MZ^n\mathbf F}\bigr)\le-\log\beta_{\epsilon'}(W,V,n).
--   $$
--
--   The paper's reason: a test for the simple binary hypothesis testing problem for $P_{M\hat MZ^n\mathbf F}$ and $Q_{M\hat MZ^n\mathbf F}$, along with the wiretap code, constitutes an active hypothesis test for $W$ and $V$. The paper uses it with $\mu$ uniform, $\epsilon'=\epsilon+\delta+\eta$ and $V$ of degraded form.
--
--   **Formalization Note** Logarithms are base 2 and $-\log\beta$ is extended-real valued. The active test observes the channel inputs, the outputs $(Y,Z)^n$ and the feedback, but not the message.
--
--   Differences from the source:
--   - generalization: an (N, n, ϵ, δ) code with uniform M, ϵ' = ϵ + δ + η < 1, V(y,z|x) = V₂(z|x)V₁(y|z) → every wiretap code, every message law μ, every channel V : X → Y × Z, every 0 ≤ ϵ' < 1; reason: the reduction (code + test = active test) uses none of these hypotheses; it specializes to the page's instance
--   - encoding: log (base fixed by ⌊2^{nR}⌋), −log β real-valued → Real.logb 2; −log β as negLog2 in EReal (+∞ at β = 0); reason: Lean convention; β = 0 is reachable and −log 0 = +∞ is the page's value
--   - encoding: (possibly randomized) encoder and feedback mappings, time index t = 1, …, n, messages {1, …, N} → deterministic maps of independent local randomness Ux, Uy of arbitrary type (paper's own representation, proof of Lemma 7), arbitrary feedback alphabet, 0-based rounds, Fin N; reason: Lean convention; the same class of codes
--   - generalization: discrete (finite) input alphabet X → any type X, with Y and Z finite; reason: neither the statement nor its proof forms a law on X or uses finiteness of X; every finite X is an instance
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, p.4, proof of Theorem 6, second display

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_testBeta
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_WiretapCode_law

namespace WiretapFeedback

/-- **Proof of Theorem 6, second display** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 4):
"a test for the simple binary hypothesis testing problem for `P_{M M̂ Zⁿ 𝐅}` and `Q_{M M̂ Zⁿ 𝐅}`
along with the wiretap code constitutes an active hypothesis test for `W` and `V`. Therefore,
`−log β_{ϵ+δ+η}(P_{M M̂ Zⁿ 𝐅}, Q_{M M̂ Zⁿ 𝐅}) ≤ −log β_{ϵ+δ+η}(W, V, n)`."

Stated for every wiretap code `c` (any `N`, `n`), every message law `μ`, every pair of channels
`W, V : X → Y × Z` and every `0 ≤ ϵ' < 1`, where `P`, `Q` are the laws of `(M, M̂, Zⁿ, 𝐅)` under
`W` and under `V`.

**Formalization Note** Base-2 logarithms, `−log β` as `negLog2` in `EReal`. The active test
observes `(Xⁿ, (Y, Z)ⁿ, 𝐅)` (not `M`), as in the paper's definition of `β_ϵ(W, V, n)`. -/
theorem negLog_beta_codeLaws_le_negLog_activeBeta {X Y Z : Type} [Fintype Y] [Fintype Z]
    {N n : ℕ} (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W V : WildeQIT.Channel X (Y × Z))
    (ε' : ℝ) (h0 : 0 ≤ ε') (h1 : ε' < 1) :
    negLog2 (testBeta ε' (c.law μ W) (c.law μ V)) ≤ negLog2 (activeBeta ε' W V n) := by sorry

end WiretapFeedback
