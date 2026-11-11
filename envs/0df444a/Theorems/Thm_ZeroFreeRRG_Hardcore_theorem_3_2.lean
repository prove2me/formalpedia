-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_3_2
-- name    : ZeroFreeRRG.Hardcore.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:38.792945+00:00
-- url     : https://prove2.me/theorems/f7711389-f80d-4061-b844-27ffe1be3b44
-- title:
--   Theorem 3.2 — reinforced small subgraph conditioning: (F_n, X) →d (W, Z) in H(D) × ℤ_{≥0}^{ℤ_{≥1}}; zero-freeness given X_1 = X_2 = 0
-- statement:
--   Let $D\subseteq\mathbb C$ be open and connected, $I\subseteq D\cap\mathbb R$ a nonempty open interval, $Y_n$ random elements of $H(D)$, $X_{\ell,n}\in\mathbb Z_{\ge0}$ ($\ell\ge1$) random variables, $\lambda_\ell>0$, $\delta_\ell\in H(D)$, $A_n=\mathbb E[Y_n]$, $F_n=Y_n/A_n$, and $Z_\ell\sim\mathrm{Poisson}(\lambda_\ell)$ independent. Assume (B0)–(B5) (Definition `RSSC`). Then $W$ converges almost surely in $H(D)$, and
--   $$\big(F_n,(X_{\ell,n})_{\ell\ge1}\big)\xrightarrow{d}\big(W,(Z_\ell)_{\ell\ge1}\big)\quad\text{in }H(D)\times\mathbb Z_{\ge0}^{\mathbb Z_{\ge1}}.$$
--   In particular, if $1+\delta_\ell$ is nowhere zero on $D$ for every $\ell\ge3$, then conditional on $X_{1,n}=X_{2,n}=0$, $Y_n$ is zero-free on each fixed compact $K\subset D$ with probability $1-o_n(1)$.
--
--   This is the paper's analytic engine: applied to the truncated normalized partition function of the configuration model it yields Theorem 5.1.
--
--   Differences from the source:
--   - encoding: H(D) with the topology of locally uniform convergence; random elements and convergence in distribution E[φ(F_n)] → E[φ(F)] for bounded continuous φ on H(D) (× ℤ_{≥0}^{ℤ_{≥1}}) → functions ℂ → ℂ holomorphic on D, as points of HFun D = ℂ →ᵤ[compacts of D] ℂ (Borel σ-algebra); test functions φ bounded continuous on HFun D (× ℕ → ℕ with the product topology); reason: values off D are topologically invisible; H(D) is closed in the metrizable quotient of HFun D, so by Tietze its bounded continuous functions are exactly restrictions of those of HFun D
--   - encoding: X_{ℓ,n}, Z_ℓ, λ_ℓ, δ_ℓ indexed by ℓ ≥ 1 → stored at index i = ℓ − 1 ∈ ℕ (X n i, Z i, lam i, δ i); reason: a shift of index; 'ℓ ≥ 3' becomes i ≥ 2 and 'X_{1,n} = X_{2,n} = 0' becomes X n 0 = X n 1 = 0
--   - encoding: random elements Y_n, X_{ℓ,n} and independent Z_ℓ ∼ Poisson(λ_ℓ) (probability space unspecified) → Y n, X n on a probability space (Ωs n, P n) for each n; Z on (Ω₀, P₀) with IsIndepPoisson (measurable, iIndepFun, law poissonMeasure λ_ℓ); reason: convergence in distribution only involves laws; one space per n covers every coupling
--   - encoding: I ⊆ D ∩ ℝ a nonempty open interval → I = Set.Ioo a b with real a < b and (t : ℂ) ∈ D for t ∈ I; reason: an unbounded interval is not of this form, but each hypothesis on I implies the same hypothesis on a bounded subinterval and no conclusion mentions I, so the bounded case is the general one
--   - encoding: Y_n(t) ≥ 0, 0 < A_n(t) → (0 : ℂ) ≤ Y n ω t, (0 : ℂ) < A_n(t) in the order of ℂ (real and nonnegative / positive); reason: same condition
--   - encoding: the formal product W(z) = ∏_{ℓ ≥ 1} (1 + δ_ℓ)^{Z_ℓ} exp{−λ_ℓ δ_ℓ} → Wlim: the pointwise limit (limUnder) of the partial products Wpartial N; reason: where the partial products converge this is W; the theorem asserts the convergence
--   - encoding: (X_{1,n}, …, X_{m,n}) →d (Z_1, …, Z_m) → convergence of every point probability P_n(X_{1..m,n} = j) → P₀(Z_{1..m} = j), j ∈ ℕ^m; reason: for ℕ^m-valued random vectors these are equivalent (Scheffé)
--   - reading: (B2) E[F_n(t) ∏_ℓ (X_{ℓ,n})_{j_ℓ}] → ∏_ℓ [λ_ℓ(1 + δ_ℓ(t))]^{j_ℓ} → the integrand is integrable for all large n, and its Bochner integral converges to the product; reason: a convergent sequence of expectations presupposes they are finite; without it Lean's junk value 0 for a non-integrable integrand would change the hypothesis
--   - encoding: (B4) E[F_n(t)²] and exp(∑ λ_ℓ δ_ℓ(t)²) → ∫⁻ |F_n(t)|² (ENNReal limsup) and exp(∑' λ_ℓ |δ_ℓ(t)|²); reason: F_n(t) ≥ 0 a.s. by (B0), and δ_ℓ(t) is real for t ∈ I under (B0) and (B2) (p. 20), so the squares equal the squared moduli
--   - encoding: sup_{z ∈ K} and ∑_{ℓ ≥ 1} … < ∞ in (B3), (B5) → ENNReal-valued ⨆ z ∈ K and ∑' (ℝ≥0∞), compared with ∞; reason: extended-real suprema and sums; no junk values
--   - encoding: 'conditional on X_{1,n} = X_{2,n} = 0, … with probability 1 − o_n(1)' → the conditional measure (P n)[|{X n 0 = 0 ∧ X n 1 = 0}] of the zero-free event tends to 1; reason: ProbabilityTheory.cond; the conditioning event has probability bounded away from 0 by (B1)
--   - encoding: W converges almost surely in H(D) → for P₀-a.e. ω the partial products converge locally uniformly on D to Wlim ω; reason: convergence in H(D) is locally uniform convergence
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), pp. 18–19, Theorem 3.2

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology

namespace ZeroFreeRRG.Hardcore

/-- **Theorem 3.2** (reinforced small subgraph conditioning; pp. 18–19). Let `D ⊆ ℂ` be open and
connected, `I = (a, b) ⊆ D ∩ ℝ` a nonempty open interval, `Y_n` random elements of `H(D)` and
`X_{ℓ,n} ∈ ℤ_{≥0}` random variables on probability spaces `(Ω_n, P_n)`, `λ_ℓ > 0`, `δ_ℓ ∈ H(D)`, and
`Z_ℓ ∼ Poisson(λ_ℓ)` independent (`ℓ ≥ 1`, stored at index `ℓ − 1`). Under (B0)–(B5), `W` converges
almost surely in `H(D)`, and `(F_n, (X_{ℓ,n})_ℓ) →d (W, (Z_ℓ)_ℓ)` in `H(D) × ℤ_{≥0}^{ℤ_{≥1}}`. In
particular, if `1 + δ_ℓ` is nowhere zero on `D` for every `ℓ ≥ 3`, then conditional on
`X_{1,n} = X_{2,n} = 0`, `Y_n` is zero-free on each fixed compact `K ⊂ D` with probability
`1 − o_n(1)`. -/
theorem theorem_3_2 (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (a b : ℝ) (hab : a < b)
    (hI : ∀ t ∈ Set.Ioo a b, (t : ℂ) ∈ D)
    {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (P : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (P n)] (Y : ∀ n, Ωs n → ℂ → ℂ) (X : ∀ n, ℕ → Ωs n → ℕ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (Z : ℕ → Ω₀ → ℕ) (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ)
    (hY : ∀ n, IsRandomHol D (Y n)) (hX : ∀ n i, Measurable (X n i))
    (hlam : ∀ i, 0 < lam i) (hδ : ∀ i, DifferentiableOn ℂ (δ i) D)
    (hZ : IsIndepPoisson P₀ Z lam)
    (hB0 : CondB0 P Y D (Set.Ioo a b)) (hB1 : CondB1 P X P₀ Z)
    (hB2 : ∀ t ∈ Set.Ioo a b, CondB2At P Y X lam δ t) (hB3 : CondB3 lam δ D)
    (hB4 : ∀ t ∈ Set.Ioo a b, CondB4At P Y lam δ t) (hB5 : CondB5 P Y D) :
    (∀ᵐ ω ∂P₀, TendstoLocallyUniformlyOn (fun N => Wpartial lam δ Z N ω) (Wlim lam δ Z ω) atTop D) ∧
    (∀ φ : HFun D × (ℕ → ℕ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (toH D (normalizedFn (P n) (Y n) ω), fun i => X n i ω) ∂(P n))
        atTop (𝓝 (∫ ω, φ (toH D (Wlim lam δ Z ω), fun i => Z i ω) ∂P₀))) ∧
    ((∀ i, 2 ≤ i → ∀ z ∈ D, 1 + δ i z ≠ 0) →
      ∀ K : Set ℂ, IsCompact K → K ⊆ D →
        Tendsto (fun n => (P n)[|{ω | X n 0 ω = 0 ∧ X n 1 ω = 0}] {ω | ∀ z ∈ K, Y n ω z ≠ 0})
          atTop (𝓝 1)) := by sorry

end ZeroFreeRRG.Hardcore
