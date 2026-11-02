-- Prove2me | Theorems.Thm_WiretapFeedback_condIndep_message_decoded
-- name    : WiretapFeedback.condIndep_message_decoded
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:01:41.529936+00:00
-- url     : https://prove2.me/theorems/fc3d0210-6025-43f2-b438-6dde3a18652c
-- title:
--   Lemma 7 — $M$ and $\hat M$ are conditionally independent given $(Z^n,\mathbf F)$ under a degraded-form channel
-- statement:
--   Let $V:\mathcal X\to\mathcal Y\times\mathcal Z$ be a wiretap channel of the form $V(y,z|x)=V_2(z|x)V_1(y|z)$ for channels $V_2:\mathcal X\to\mathcal Z$ and $V_1:\mathcal Z\to\mathcal Y$. Fix a wiretap code with public feedback and a random message $M$ with any law $\mu$, let $\hat M=d(Y^n)$ and let $\mathbf F$ be the corresponding feedback. Then the induced law $Q_{M\hat MZ^n\mathbf F}$ satisfies the factorization condition
--   $$
--   Q_{M\hat M|Z^n\mathbf F}=Q_{M|Z^n\mathbf F}\times Q_{\hat M|Z^n\mathbf F}.
--   $$
--
--   This is what makes the code's law under $V$ an admissible alternative hypothesis $Q$ in Theorem 5.
--
--   **Formalization Note** The factorization is stated without division: $Q(m,\hat m,z,f)\,Q_{Z^n\mathbf F}(z,f)=Q_{MZ^n\mathbf F}(m,z,f)\,Q_{\hat MZ^n\mathbf F}(\hat m,z,f)$ for all $m,\hat m,z,f$.
--
--   Differences from the source:
--   - reading: a random message M (law not specified; Theorem 6 uses the uniform law) → any message law μ on Fin N; reason: the lemma fixes no law and its proof uses none; the uniform case of Theorem 6 is an instance
--   - encoding: Q_{MM̂|Zⁿ𝐅} = Q_{M|Zⁿ𝐅} × Q_{M̂|Zⁿ𝐅} → Q(m,m̂,z,f)·Q_{Zⁿ𝐅}(z,f) = Q_{MZⁿ𝐅}(m,z,f)·Q_{M̂Zⁿ𝐅}(m̂,z,f); reason: equivalent where Q_{Zⁿ𝐅}(z,f) > 0 and automatic elsewhere
--   - encoding: a channel V with V(y,z|x) = V₂(z|x)V₁(y|z) → V with hypothesis ∀ x y z, V(y,z|x) = V₂(z|x)·V₁(y|z) for channels V₂, V₁; reason: Lean convention; the same channels
--   - encoding: (possibly randomized) encoder and feedback mappings, time index t = 1, …, n, messages {1, …, N} → deterministic maps of independent local randomness Ux, Uy of arbitrary type (paper's own representation, proof of Lemma 7), arbitrary feedback alphabet, 0-based rounds, Fin N; reason: Lean convention; the same class of codes
--   - generalization: discrete (finite) input alphabet X → any type X, with Y and Z finite; reason: neither the statement nor its proof forms a law on X or uses finiteness of X; every finite X is an instance
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, p.3, Lemma 7

import Mathlib
import Definitions.Def_WiretapFeedback_WiretapCode_law

namespace WiretapFeedback

/-- **Lemma 7** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3). For a wiretap channel
`V : X → Y × Z` such that `V(y, z|x) = V₂(z|x) V₁(y|z)`, a random message `M`, and a wiretap code,
let `M̂ = d(Yⁿ)` and `𝐅` be the corresponding feedback. Then the induced distribution
`Q_{M M̂ Zⁿ 𝐅}` satisfies the factorization condition
`Q_{M M̂|Zⁿ 𝐅} = Q_{M|Zⁿ 𝐅} × Q_{M̂|Zⁿ 𝐅}`.

**Formalization Note** "A random message `M`" is a message with an arbitrary law `μ` on `Fin N`.
The factorization is stated division-free,
`Q(m, m̂, z, f) Q_{Zⁿ𝐅}(z, f) = Q_{M Zⁿ 𝐅}(m, z, f) Q_{M̂ Zⁿ 𝐅}(m̂, z, f)`, which is the paper's
identity wherever `Q_{Zⁿ𝐅}(z, f) > 0` and holds trivially elsewhere. The channels `V₂ : X → Z`
and `V₁ : Z → Y` are stochastic matrices on finite alphabets. -/
theorem condIndep_message_decoded {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}
    (V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (c : WiretapCode X Y N n) (μ : PMF (Fin N)) :
    ∀ (m m' : Fin N) (z : Fin n → Z) (f : Fin n → c.Fb),
      c.law μ V (m, m', z, f) * ((c.law μ V).map fun t => t.2.2) (z, f) =
        ((c.law μ V).map fun t => (t.1, t.2.2)) (m, z, f) *
          ((c.law μ V).map fun t => (t.2.1, t.2.2)) (m', z, f) := by sorry

end WiretapFeedback
