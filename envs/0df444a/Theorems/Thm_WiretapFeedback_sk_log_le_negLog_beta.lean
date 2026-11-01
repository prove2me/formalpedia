-- Prove2me | Theorems.Thm_WiretapFeedback_sk_log_le_negLog_beta
-- name    : WiretapFeedback.sk_log_le_negLog_beta
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:49.138535+00:00
-- url     : https://prove2.me/theorems/f5d13968-7fea-40fb-8884-20f4f49641e4
-- title:
--   Theorem 5 — secret-key length bounded by a hypothesis-testing exponent
-- statement:
--   Let $0\le\epsilon,\delta$ with $\epsilon+\delta<1$. Let $K,\hat K$ take values in a set of $k\ge1$ elements and $Z$ in an arbitrary alphabet, with joint law $P_{K\hat KZ}$ such that
--   $$
--   P(K\ne\hat K)\le\epsilon\qquad\text{and}\qquad\|P_{KZ}-P_{\mathrm{unif}}\times P_Z\|_1\le\delta,
--   $$
--   where $P_{\mathrm{unif}}$ is the uniform distribution on the $k$ values. Then for every $0<\eta<1-\epsilon-\delta$ and every distribution $Q_{K\hat KZ}=Q_{K|Z}Q_{\hat K|Z}Q_Z$ under which $K$ and $\hat K$ are conditionally independent given $Z$,
--   $$
--   \log k\le-\log\beta_{\epsilon+\delta+\eta}\bigl(P_{K\hat KZ},Q_{K\hat KZ}\bigr)+2\log\frac1\eta .
--   $$
--
--   The result is cited in the paper from Tyagi–Watanabe (EUROCRYPT 2014, Lemma 1; arXiv:1404.5715) and not proved there. It reduces secret-key agreement to binary hypothesis testing; applied with $K=M$, $\hat K=\hat M$ and $Z=(Z^n,\mathbf F)$ it yields the first step of the proof of Theorem 6.
--
--   **Formalization Note** Logarithms are base 2 and $-\log\beta$ is extended-real valued. The conditional independence under $Q$ is stated without division, as $Q(a,b,z)\,Q_Z(z)=Q_{KZ}(a,z)\,Q_{\hat KZ}(b,z)$ for all $a,b,z$.
--
--   Differences from the source:
--   - encoding: log (base fixed by ⌊2^{nR}⌋), −log β real-valued → Real.logb 2; −log β as negLog2 in EReal (+∞ at β = 0); reason: Lean convention; β = 0 is reachable and −log 0 = +∞ is the page's value
--   - encoding: K, K̂ with k values, k unspecified → Fin k with k ≥ 1 ([NeZero k]); reason: P_unif on k values exists only for k ≥ 1
--   - encoding: Q_{KK̂Z} = Q_{K|Z} Q_{K̂|Z} Q_Z → ∀ a b z, Q(a,b,z)·Q_Z(z) = Q_{KZ}(a,z)·Q_{K̂Z}(b,z); reason: equivalent where Q_Z(z) > 0 and automatic where Q_Z(z) = 0
--   - encoding: random variables K, K̂, Z → a joint probability mass function on Fin k × Fin k × Z' with Z' an arbitrary type; reason: discrete random variables are their joint law; Z' arbitrary because the theorem is applied with Z = (Zⁿ, 𝐅)
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §IV, p.3, Theorem 5

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_tvDist
import Definitions.Def_WiretapFeedback_testBeta

namespace WiretapFeedback

/-- **Theorem 5** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3; cited there from Tyagi–Watanabe
[17, Lemma 1], [18], not proved in the paper). For `0 ≤ ϵ, δ`, `ϵ + δ < 1`, let `K, K̂` take values
in `{1, …, k}` and `Z` in any alphabet, with joint law `P = P_{K K̂ Z}` such that
`P(K ≠ K̂) ≤ ϵ` and `‖P_{KZ} − P_unif × P_Z‖₁ ≤ δ`, where `P_unif` is uniform on `k` values. Then
for every `0 < η < 1 − ϵ − δ` and every `Q_{K K̂ Z} = Q_{K|Z} Q_{K̂|Z} Q_Z`,
`log k ≤ −log β_{ϵ+δ+η}(P_{K K̂ Z}, Q_{K K̂ Z}) + 2 log (1/η)`.

**Formalization Note** `{1, …, k}` is `Fin k` with `k ≥ 1` (`[NeZero k]`, needed for `P_unif`).
The factorization `Q_{K K̂|Z} = Q_{K|Z} Q_{K̂|Z}` is stated division-free,
`Q(a, b, z) Q_Z(z) = Q_{KZ}(a, z) Q_{K̂Z}(b, z)`, equivalent wherever `Q_Z(z) > 0` and automatic
elsewhere. Logarithms are base 2; `−log β` is `negLog2` (`+∞` at `β = 0`), so the inequality is in
`EReal`. `Z'` is an arbitrary type, as the theorem is applied with `Z = (Zⁿ, 𝐅)`. -/
theorem sk_log_le_negLog_beta {Z' : Type} (k : ℕ) [NeZero k] (ε δ η : ℝ) (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) (P Q : PMF (Fin k × Fin k × Z'))
    (hP_err : P.toOuterMeasure {t | t.1 ≠ t.2.1} ≤ ENNReal.ofReal ε)
    (hP_sec : tvDist (P.map fun t => (t.1, t.2.2))
        ((PMF.uniformOfFintype (Fin k)).bind fun a => (P.map fun t => t.2.2).map fun z => (a, z))
      ≤ ENNReal.ofReal δ)
    (hQ : ∀ (a b : Fin k) (z : Z'), Q (a, b, z) * (Q.map fun t => t.2.2) z =
        (Q.map fun t => (t.1, t.2.2)) (a, z) * (Q.map fun t => (t.2.1, t.2.2)) (b, z))
    (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 k : ℝ) : EReal) ≤
      negLog2 (testBeta (ε + δ + η) P Q) + ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by sorry

end WiretapFeedback
