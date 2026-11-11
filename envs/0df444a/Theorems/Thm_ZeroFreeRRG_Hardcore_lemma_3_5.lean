-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_3_5
-- name    : ZeroFreeRRG.Hardcore.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:37.108198+00:00
-- url     : https://prove2.me/theorems/8d3f125c-208d-43e9-9ea6-62b2280040ea
-- title:
--   Lemma 3.5 — tightness of {F_n}_{n≥n₀} in H(D) under (B0) and (B5)
-- statement:
--   In the setting of Theorem 3.2 ($D$ open connected, $I\subseteq D\cap\mathbb R$ a nonempty open interval, $Y_n$ random elements of $H(D)$, $F_n=Y_n/A_n$), assume (B0) and (B5). Then for every sufficiently large $n_0$ the tail $\{F_n\}_{n\ge n_0}$ is tight in $H(D)$: for every $\varepsilon>0$ there is a compact $\mathcal C_\varepsilon\subseteq H(D)$ with
--   $$\inf_{n\ge n_0}\Pr[F_n\in\mathcal C_\varepsilon]\ge1-\varepsilon .$$
--   With Prokhorov's theorem this gives subsequential limits in Theorem 3.2.
--
--   Differences from the source:
--   - encoding: H(D) with the topology of locally uniform convergence; random elements and convergence in distribution E[φ(F_n)] → E[φ(F)] for bounded continuous φ on H(D) (× ℤ_{≥0}^{ℤ_{≥1}}) → functions ℂ → ℂ holomorphic on D, as points of HFun D = ℂ →ᵤ[compacts of D] ℂ (Borel σ-algebra); test functions φ bounded continuous on HFun D (× ℕ → ℕ with the product topology); reason: values off D are topologically invisible; H(D) is closed in the metrizable quotient of HFun D, so by Tietze its bounded continuous functions are exactly restrictions of those of HFun D
--   - encoding: random elements Y_n, X_{ℓ,n} and independent Z_ℓ ∼ Poisson(λ_ℓ) (probability space unspecified) → Y n, X n on a probability space (Ωs n, P n) for each n; Z on (Ω₀, P₀) with IsIndepPoisson (measurable, iIndepFun, law poissonMeasure λ_ℓ); reason: convergence in distribution only involves laws; one space per n covers every coupling
--   - encoding: I ⊆ D ∩ ℝ a nonempty open interval → I = Set.Ioo a b with real a < b and (t : ℂ) ∈ D for t ∈ I; reason: an unbounded interval is not of this form, but each hypothesis on I implies the same hypothesis on a bounded subinterval and no conclusion mentions I, so the bounded case is the general one
--   - encoding: Y_n(t) ≥ 0, 0 < A_n(t) → (0 : ℂ) ≤ Y n ω t, (0 : ℂ) < A_n(t) in the order of ℂ (real and nonnegative / positive); reason: same condition
--   - encoding: sup_{z ∈ K} and ∑_{ℓ ≥ 1} … < ∞ in (B3), (B5) → ENNReal-valued ⨆ z ∈ K and ∑' (ℝ≥0∞), compared with ∞; reason: extended-real suprema and sums; no junk values
--   - encoding: tight: compact K_ε ⊆ H(D) with inf_{n≥n₀} Pr[F_n ∈ K_ε] ≥ 1 − ε → IsCompact 𝒞 in HFun D, 𝒞 ⊆ HSet D, and 1 − ε ≤ P_n(F_n ∈ 𝒞) for every n ≥ n₀; reason: compactness in the subspace H(D) is compactness of a subset of H(D) in the ambient space; an infimum bound is a bound for each n
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 20, Lemma 3.5

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open MeasureTheory ProbabilityTheory Filter

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 3.5** (tightness; p. 20). In the setting of Theorem 3.2 (`D` open connected, `I ⊆ D ∩ ℝ`
a nonempty open interval, `Y_n` random elements of `H(D)` on probability spaces `(Ω_n, P_n)`),
under (B0) and (B5) the tail `{F_n}_{n ≥ n₀}` of `F_n = Y_n / A_n` is tight in `H(D)` for every
sufficiently large `n₀`: for every `ε > 0` there is a compact `𝒞_ε ⊆ H(D)` with
`P_n(F_n ∈ 𝒞_ε) ≥ 1 − ε` for all `n ≥ n₀`. -/
theorem lemma_3_5 (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (a b : ℝ) (hab : a < b)
    (hI : ∀ t ∈ Set.Ioo a b, (t : ℂ) ∈ D)
    {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (P : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (P n)] (Y : ∀ n, Ωs n → ℂ → ℂ)
    (hY : ∀ n, IsRandomHol D (Y n))
    (hB0 : CondB0 P Y D (Set.Ioo a b)) (hB5 : CondB5 P Y D) :
    ∃ N₀ : ℕ, ∀ n₀ ≥ N₀, ∀ ε : ℝ, 0 < ε →
      ∃ 𝒞 : Set (HFun D), IsCompact 𝒞 ∧ 𝒞 ⊆ HSet D ∧
        ∀ n ≥ n₀, 1 - ε ≤ (P n).real {ω | toH D (normalizedFn (P n) (Y n) ω) ∈ 𝒞} := by sorry

end ZeroFreeRRG.Hardcore
