-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_6
-- name    : Z2PostSamp.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:41.602292+00:00
-- url     : https://prove2.me/theorems/8c66ab4c-32d9-4f6c-8685-cf6b311f2c83
-- title:
--   Lemma 3.6 — finite-dimensional cavity moment input: $(I-C_{\mathrm{cav}})z=N^{-1}(1-q^2,q-q^2,p-q^2)^\top+\delta$ with the bound (3.4), and the eigenvalues of $C_{\mathrm{cav}}$
-- statement:
--   Consider the Gaussian model of §3.1 with $q>0$, and suppose that $\Lambda=r+t/q$ belongs to a fixed compact subinterval of $(1,\infty)$. Set $p=\mathbb E\tanh^4(rq+t+\sqrt{rq+t}\,G)$, $G\sim\mathcal N(0,1)$, and define
--
--   $$z=\begin{pmatrix}\mathbb E\langle(R_{1\theta}-q)^2\rangle\\\mathbb E\langle(R_{1\theta}-q)(R_{2\theta}-q)\rangle\\\mathbb E\langle(R_{1\theta}-q)(R_{23}-q)\rangle\end{pmatrix},\qquad C_{\mathrm{cav}}=r\begin{pmatrix}1-q^2&-2(q-q^2)&p-q^2\\q-q^2&1-q-2p+2q^2&-2q+3p-q^2\\p-q^2&4q-6p+2q^2&1-6q+6p-q^2\end{pmatrix}.$$
--
--   There is a remainder vector $\delta\in\mathbb R^3$ such that
--
--   $$(I-C_{\mathrm{cav}})z=\frac1N\begin{pmatrix}1-q^2\\q-q^2\\p-q^2\end{pmatrix}+\delta,\tag{3.3}$$
--
--   $$\|\delta\|_\infty\le C\Big\{\mathbb E\langle|R_{12}-q|^3\rangle+\frac1N\mathbb E\langle(R_{12}-q)^2\rangle+\frac1N\mathbb E\langle|R_{12}-q|\rangle+\frac1{N^2}\Big\},\tag{3.4}$$
--
--   where $C$ depends only on the compact interval for $\Lambda$, uniformly in $N$ and in $\tau=r/\Lambda\in[0,1]$. The eigenvalues of $C_{\mathrm{cav}}$ are $r(1-2q+p)$, with algebraic multiplicity two, and $r(1-3q+2p)$.
--
--   This Rademacher specialization of the El Alaoui–Krzakala–Jordan cavity system converts overlap concentration at a fixed tolerance into the $O(N^{-1})$ second moment of Lemma 3.7.
--
--   **Formalization Note** The interval is $[\Lambda_1,\Lambda_2]$ with $1<\Lambda_1$; the model has $r,t\ge0$, so $\tau\in[0,1]$. The remainder is defined by (3.3), so the existence claim is (3.4) for that $\delta$. The expectations are Bochner integrals of bounded measurable functions of the Gaussian sample, hence genuine. The eigenvalue clause is the factorization of the characteristic polynomial.
--
--   Differences from the source:
--   - encoding: there is a remainder vector δ with (3.3) and (3.4) → δ := (I − C_cav)z − N^{−1}(1 − q², q − q², p − q²)ᵀ satisfies (3.4); reason: (3.3) determines δ
--   - encoding: the eigenvalues of C_cav are r(1 − 2q + p) (algebraic multiplicity two) and r(1 − 3q + 2p) → charpoly C_cav = (X − r(1 − 2q + p))² (X − r(1 − 3q + 2p)); reason: algebraic multiplicities are the multiplicities of the roots of the characteristic polynomial
--   - encoding: a fixed compact subinterval of (1, ∞) for Λ → [Λ₁, Λ₂] with 1 < Λ₁ ≤ Λ₂; reason: every compact subinterval has this form
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.6, p.17, (3.3)–(3.4)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Construction
import Definitions.Def_Z2PostSamp_GaussModel

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 3.6 (finite-dimensional cavity moment input).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.6, p.17: "Consider the Gaussian model above with `q > 0`, and suppose that
`Λ = r + t/q` belongs to a fixed compact subinterval of `(1, ∞)`. Set
`p = E tanh⁴(rq + t + √(rq + t) G)`, `G ∼ N(0,1)`, and define
`z = (E⟨(R_{1θ} − q)²⟩, E⟨(R_{1θ} − q)(R_{2θ} − q)⟩, E⟨(R_{1θ} − q)(R_{23} − q)⟩)ᵀ`,
`C_cav = r [[1 − q², −2(q − q²), p − q²], [q − q², 1 − q − 2p + 2q², −2q + 3p − q²],
[p − q², 4q − 6p + 2q², 1 − 6q + 6p − q²]]`. There is a remainder vector `δ ∈ ℝ³` such that
`(I − C_cav) z = (1/N)(1 − q², q − q², p − q²)ᵀ + δ` (3.3), and
`‖δ‖_∞ ≤ C{E⟨|R_{12} − q|³⟩ + (1/N)E⟨(R_{12} − q)²⟩ + (1/N)E⟨|R_{12} − q|⟩ + 1/N²}` (3.4). Here `C`
depends only on the compact interval for `Λ`, uniformly in `N` and in `τ = r/Λ ∈ [0, 1]`. The
eigenvalues of `C_cav` are `r(1 − 2q + p)`, with algebraic multiplicity two, and `r(1 − 3q + 2p)`."

**Formalization Note.** The compact subinterval is `[Λ₁, Λ₂]` with `1 < Λ₁`; the Gaussian model
has `r, t ≥ 0` (§3.1) and `q = posRoot r t`, so `τ = r/Λ ∈ [0,1]` automatically. The remainder is
**defined** by (3.3), so "there is `δ` with (3.3) and (3.4)" is (3.4) for that `δ`. The entries of `z`
and the expectations in (3.4) are Bochner integrals of bounded measurable functions of the
Gaussian sample (posterior averages of bounded quantities), hence genuine expectations. The
eigenvalue clause is the factorization of the characteristic polynomial (algebraic multiplicities). -/
theorem lemma_3_6 (Λ₁ Λ₂ : ℝ) (h1 : 1 < Λ₁) (h12 : Λ₁ ≤ Λ₂) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → 0 ≤ t → 0 < posRoot r t →
      Λ₁ ≤ r + t / posRoot r t → r + t / posRoot r t ≤ Λ₂ →
      let q := posRoot r t
      let p := ∫ g, Real.tanh (r * q + t + Real.sqrt (r * q + t) * g) ^ 4 ∂(gaussianReal 0 1)
      let z : Fin 3 → ℝ :=
        ![∫ ω, lawMean (gpost r t ω) (fun σ => (overlap σ ω.1 - q) ^ 2) ∂(gaussLaw N),
          ∫ ω, avg2 (gpost r t ω) (fun σ τ => (overlap σ ω.1 - q) * (overlap τ ω.1 - q))
            ∂(gaussLaw N),
          ∫ ω, avg3 (gpost r t ω) (fun σ τ ρ => (overlap σ ω.1 - q) * (overlap τ ρ - q))
            ∂(gaussLaw N)]
      let Ccav : Matrix (Fin 3) (Fin 3) ℝ := r • !![1 - q ^ 2, -2 * (q - q ^ 2), p - q ^ 2;
          q - q ^ 2, 1 - q - 2 * p + 2 * q ^ 2, -2 * q + 3 * p - q ^ 2;
          p - q ^ 2, 4 * q - 6 * p + 2 * q ^ 2, 1 - 6 * q + 6 * p - q ^ 2]
      let δ : Fin 3 → ℝ := (1 - Ccav) *ᵥ z - (1 / (N : ℝ)) • ![1 - q ^ 2, q - q ^ 2, p - q ^ 2]
      (∀ i, |δ i| ≤ C * (∫ ω, avg2 (gpost r t ω) (fun σ τ => |overlap σ τ - q| ^ 3) ∂(gaussLaw N)
          + (1 / (N : ℝ)) * ∫ ω, avg2 (gpost r t ω) (fun σ τ => (overlap σ τ - q) ^ 2)
              ∂(gaussLaw N)
          + (1 / (N : ℝ)) * ∫ ω, avg2 (gpost r t ω) (fun σ τ => |overlap σ τ - q|) ∂(gaussLaw N)
          + 1 / (N : ℝ) ^ 2)) ∧
      Ccav.charpoly = (Polynomial.X - Polynomial.C (r * (1 - 2 * q + p))) ^ 2 *
        (Polynomial.X - Polynomial.C (r * (1 - 3 * q + 2 * p))) := by sorry

end Z2PostSamp
