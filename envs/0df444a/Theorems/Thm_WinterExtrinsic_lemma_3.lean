-- Prove2me | Theorems.Thm_WinterExtrinsic_lemma_3
-- name    : WinterExtrinsic.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:13.116568+00:00
-- url     : https://prove2.me/theorems/7348bae7-03d4-443d-b338-8588d2ad8adb
-- title:
--   Lemma 3 — Ahlswede–Winter operator Chernoff bound (corrected constant)
-- statement:
--   Let $\mathcal K$ be a finite-dimensional complex Hilbert space and let $X_1, \dots, X_M$ ($M \ge 1$) be independent, identically distributed random operators on $\mathcal K$ with $0 \le X_\mu \le \mathbb 1$ in the operator order. Suppose the mean $\sigma = \mathbb E X_\mu$ satisfies $\sigma \ge s\mathbb 1$ for a real number $s$. Then for every $0 < \eta < 1/2$
--
--   $$\Pr\Big\{ \frac1M \sum_{\mu=1}^M X_\mu \notin [(1-\eta)\sigma;\,(1+\eta)\sigma] \Big\} \le 2 \dim\mathcal K \cdot \exp_2\!\Big( -M\,\frac{\eta^2 s}{2(1+\eta)\ln 2} \Big),$$
--
--   where $[A; B] = \{X : A \le X \le B\}$ is an interval in the operator order and $\exp_2(x) = 2^x$ (the paper's logs and exps are to base 2). Since $2^{-x/\ln 2} = e^{-x}$, the right side equals $2\dim\mathcal K\, e^{-M\eta^2 s/(2(1+\eta))}$.
--
--   This relative operator Chernoff bound is the probabilistic engine of the proof of Theorem 2: it shows that a random sample of $M$ typical words reproduces the average operator $\Omega$ within a factor $1 \pm \epsilon$ (event $(\mathrm I_\nu)$) and the distribution $L'$ (event $(\mathrm{II})$).
--
--   **Formalization Note** $\mathcal K = \mathbb C^\kappa$ for a finite type $\kappa$, so $\dim\mathcal K = |\kappa|$. The operator order is the Loewner order, written with `PosSemidef`; $0 \le X_\mu \le \mathbb 1$ is `IsEffect`, almost surely. The mean is entrywise, $\sigma_{ab} = \int (X_\mu)_{ab}\, d\Pr$ (the entries are bounded, hence integrable). Matrices carry the entrywise Borel σ-algebra. No sign condition is placed on $s$, as on the page.
--
--   Differences from the source:
--   - correction: bound $2\dim\mathcal K \exp(-M\eta^2 s/(2\ln 2))$ → $2\dim\mathcal K \exp(-M\eta^2 s/(2(1+\eta)\ln 2))$; reason: the printed bound is false with exp to base 2 (dim $\mathcal K$ = 1, $X_\mu$ Bernoulli(0.01), η = 0.45, M = 200 000: the probability is 1.66·10⁻⁸⁰, the printed bound 2.27·10⁻⁸⁸); the upper-tail rate $s((1+\eta)\ln(1+\eta) - \eta)$ is below $s\eta^2/2$.
--   - encoding: operators on $\mathcal K$, the operator order, $\mathbb E X_\mu$, $0 \le X_\mu \le \mathbb 1$ → matrices indexed by a finite type, `PosSemidef` differences, entrywise integrals, `IsEffect` almost surely; reason: Lean representation; random variables are determined up to null sets, so the probability is unchanged.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §II, Lemma 3, p.4 (Ahlswede, Winter [2], thm. A.19); exp to base 2, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

namespace WinterExtrinsic

open MeasureTheory ProbabilityTheory
open QAlgorithms
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Renew46.P43 (exp2)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Lemma 3 (Ahlswede–Winter operator Chernoff bound), with corrected constant. Let
`X_1, …, X_M` be i.i.d. random operators on a finite-dimensional space `𝒦`, with
`0 ≤ X_μ ≤ 1`, and average `E X_μ = σ ≥ s·1`. Then for every `0 < η < 1/2`
`Pr{(1/M) Σ_μ X_μ ∉ [(1 − η)σ; (1 + η)σ]} ≤ 2 dim 𝒦 · 2^{−M η² s / (2(1+η) ln 2)}`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§II, Lemma 3, p.4 (Ahlswede, Winter [2], thm. A.19), with exp to base 2 (p.2).

**Correction.** The page has `2 ln 2` in place of `2(1+η) ln 2`; that is false (dim 𝒦 = 1,
`X_μ` Bernoulli(0.01), η = 0.45, M = 200 000: the probability is 1.66·10⁻⁸⁰, the printed bound
2.27·10⁻⁸⁸).

**Formalization Note.** `𝒦 = ℂ^κ` for a finite type `κ`; `dim 𝒦 = Fintype.card κ`. The operator
order is the Loewner order, written with `PosSemidef`: `A ≤ B` iff `(B − A).PosSemidef`;
`0 ≤ X ≤ 1` is `IsEffect`. The expectation is entrywise
(`σ a b = ∫ (X μ ω) a b dP`); the entries are bounded, so they are integrable. Matrices carry the
entrywise Borel σ-algebra (`matrixMeasurableSpace` of the Renew46.P43 layer). Identical
distribution is stated against `X_1` (`X ⟨0, hM⟩`). No sign condition on `s` is assumed, as on
the page. -/
theorem lemma_3 {Ω κ : Type} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ) (hM : 0 < M)
    (X : Fin M → Ω → Matrix κ κ ℂ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X ⟨0, hM⟩) μ μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, IsEffect (X i ω))
    (σ : Matrix κ κ ℂ) (hσ : ∀ i a b, σ a b = ∫ ω, X i ω a b ∂μ)
    (s : ℝ) (hs : (σ - (s : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (μ {ω | ¬ ((((M : ℂ)⁻¹ • ∑ i, X i ω) - ((1 - η : ℝ) : ℂ) • σ).PosSemidef ∧
        ((((1 + η : ℝ) : ℂ) • σ) - (M : ℂ)⁻¹ • ∑ i, X i ω).PosSemidef)}).toReal ≤
      2 * Fintype.card κ * exp2 (-(M * η ^ 2 * s) / (2 * (1 + η) * Real.log 2)) := by sorry

end WinterExtrinsic
