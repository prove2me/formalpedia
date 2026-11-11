-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_3_4
-- name    : ZeroFreeRRG.Hardcore.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:23.709579+00:00
-- url     : https://prove2.me/theorems/397e9350-9ce9-4443-8031-400f369fe283
-- title:
--   Lemma 3.4 — W_N → W almost surely in H(D); given Z_1 = Z_2 = 0, W is a.s. nowhere zero
-- statement:
--   Let $D\subseteq\mathbb C$ be open and connected, $\lambda_\ell>0$, $\delta_\ell$ holomorphic on $D$, and $Z_\ell\sim\mathrm{Poisson}(\lambda_\ell)$ independent ($\ell\ge1$). Under (B3), $\sum_\ell\lambda_\ell\sup_K|\delta_\ell|^2<\infty$ for every compact $K\subset D$, the partial products $W_N=\prod_{\ell\le N}(1+\delta_\ell)^{Z_\ell}e^{-\lambda_\ell\delta_\ell}$ converge almost surely in $H(D)$ to $W$. Moreover, if $1+\delta_\ell$ is nowhere zero on $D$ for every $\ell\ge3$, then conditional on $Z_1=Z_2=0$,
--   $$W(z)\neq0\quad\text{for all }z\in D,\ \text{almost surely}.$$
--   It makes the limit object of Theorem 3.2 well defined and zero-free.
--
--   Differences from the source:
--   - encoding: X_{ℓ,n}, Z_ℓ, λ_ℓ, δ_ℓ indexed by ℓ ≥ 1 → stored at index i = ℓ − 1 ∈ ℕ (X n i, Z i, lam i, δ i); reason: a shift of index; 'ℓ ≥ 3' becomes i ≥ 2 and 'X_{1,n} = X_{2,n} = 0' becomes X n 0 = X n 1 = 0
--   - encoding: random elements Y_n, X_{ℓ,n} and independent Z_ℓ ∼ Poisson(λ_ℓ) (probability space unspecified) → Y n, X n on a probability space (Ωs n, P n) for each n; Z on (Ω₀, P₀) with IsIndepPoisson (measurable, iIndepFun, law poissonMeasure λ_ℓ); reason: convergence in distribution only involves laws; one space per n covers every coupling
--   - encoding: the formal product W(z) = ∏_{ℓ ≥ 1} (1 + δ_ℓ)^{Z_ℓ} exp{−λ_ℓ δ_ℓ} → Wlim: the pointwise limit (limUnder) of the partial products Wpartial N; reason: where the partial products converge this is W; the theorem asserts the convergence
--   - encoding: sup_{z ∈ K} and ∑_{ℓ ≥ 1} … < ∞ in (B3), (B5) → ENNReal-valued ⨆ z ∈ K and ∑' (ℝ≥0∞), compared with ∞; reason: extended-real suprema and sums; no junk values
--   - encoding: W_N → W almost surely in H(D) → for P₀-a.e. ω, TendstoLocallyUniformlyOn (W_N(ω)) (Wlim ω) on D; reason: convergence in H(D) is locally uniform convergence on D
--   - encoding: conditional on Z_1 = Z_2 = 0, almost surely → ∀ᵐ ω for the conditional measure P₀[|{Z 0 = 0 ∧ Z 1 = 0}]; reason: ProbabilityTheory.cond; the event has positive probability e^{−λ_1−λ_2}
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 19, Lemma 3.4

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 3.4** (well-definedness and nonvanishing of `W`; p. 19). Let `D ⊆ ℂ` be open and
connected, `λ_ℓ > 0`, `δ_ℓ` holomorphic on `D`, and `Z_ℓ ∼ Poisson(λ_ℓ)` independent (`ℓ ≥ 1`,
stored at index `ℓ − 1`). Under (B3), the partial products `W_N` converge almost surely in `H(D)`
(locally uniformly on `D`) to `W`. Moreover, if `1 + δ_ℓ` is nowhere zero on `D` for every `ℓ ≥ 3`,
then conditional on `Z_1 = Z_2 = 0`, `W` is almost surely nowhere zero on `D`. -/
theorem lemma_3_4 (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (Z : ℕ → Ω₀ → ℕ) (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ)
    (hlam : ∀ i, 0 < lam i) (hδ : ∀ i, DifferentiableOn ℂ (δ i) D)
    (hZ : IsIndepPoisson P₀ Z lam) (hB3 : CondB3 lam δ D) :
    (∀ᵐ ω ∂P₀, TendstoLocallyUniformlyOn (fun N => Wpartial lam δ Z N ω) (Wlim lam δ Z ω) atTop D) ∧
    ((∀ i, 2 ≤ i → ∀ z ∈ D, 1 + δ i z ≠ 0) →
      ∀ᵐ ω ∂(P₀[|{ω | Z 0 ω = 0 ∧ Z 1 ω = 0}]), ∀ z ∈ D, Wlim lam δ Z ω z ≠ 0) := by sorry

end ZeroFreeRRG.Hardcore
