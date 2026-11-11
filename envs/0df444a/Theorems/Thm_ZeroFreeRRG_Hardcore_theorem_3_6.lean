-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_3_6
-- name    : ZeroFreeRRG.Hardcore.theorem_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:33.868956+00:00
-- url     : https://prove2.me/theorems/694db311-fe44-48fd-aa87-14a7fe2e5f9f
-- title:
--   Theorem 3.6 — Janson's real-line small subgraph conditioning: (F_n(t), X_{1..m,n}) →d (W(t), Z_{1..m})
-- statement:
--   In the notation of Theorem 3.2, fix $t\in I$ and suppose $Y_n(t)\ge0$ almost surely, $0<A_n(t)=\mathbb E[Y_n(t)]<\infty$ for all sufficiently large $n$, conditions (B1)–(B2) and (B4) hold at $t$, and $\sum_{\ell\ge1}\lambda_\ell\delta_\ell(t)^2<\infty$. Then for every $m\ge1$
--   $$\big(F_n(t),X_{1,n},\dots,X_{m,n}\big)\xrightarrow{d}\big(W(t),Z_1,\dots,Z_m\big).$$
--   It identifies the limit of Theorem 3.2 on the real interval $I$.
--
--   Differences from the source:
--   - encoding: X_{ℓ,n}, Z_ℓ, λ_ℓ, δ_ℓ indexed by ℓ ≥ 1 → stored at index i = ℓ − 1 ∈ ℕ (X n i, Z i, lam i, δ i); reason: a shift of index; 'ℓ ≥ 3' becomes i ≥ 2 and 'X_{1,n} = X_{2,n} = 0' becomes X n 0 = X n 1 = 0
--   - encoding: random elements Y_n, X_{ℓ,n} and independent Z_ℓ ∼ Poisson(λ_ℓ) (probability space unspecified) → Y n, X n on a probability space (Ωs n, P n) for each n; Z on (Ω₀, P₀) with IsIndepPoisson (measurable, iIndepFun, law poissonMeasure λ_ℓ); reason: convergence in distribution only involves laws; one space per n covers every coupling
--   - encoding: I ⊆ D ∩ ℝ a nonempty open interval → I = Set.Ioo a b with real a < b and (t : ℂ) ∈ D for t ∈ I; reason: an unbounded interval is not of this form, but each hypothesis on I implies the same hypothesis on a bounded subinterval and no conclusion mentions I, so the bounded case is the general one
--   - encoding: Y_n(t) ≥ 0, 0 < A_n(t) → (0 : ℂ) ≤ Y n ω t, (0 : ℂ) < A_n(t) in the order of ℂ (real and nonnegative / positive); reason: same condition
--   - encoding: the formal product W(z) = ∏_{ℓ ≥ 1} (1 + δ_ℓ)^{Z_ℓ} exp{−λ_ℓ δ_ℓ} → Wlim: the pointwise limit (limUnder) of the partial products Wpartial N; reason: where the partial products converge this is W; the theorem asserts the convergence
--   - encoding: (X_{1,n}, …, X_{m,n}) →d (Z_1, …, Z_m) → convergence of every point probability P_n(X_{1..m,n} = j) → P₀(Z_{1..m} = j), j ∈ ℕ^m; reason: for ℕ^m-valued random vectors these are equivalent (Scheffé)
--   - reading: (B2) E[F_n(t) ∏_ℓ (X_{ℓ,n})_{j_ℓ}] → ∏_ℓ [λ_ℓ(1 + δ_ℓ(t))]^{j_ℓ} → the integrand is integrable for all large n, and its Bochner integral converges to the product; reason: a convergent sequence of expectations presupposes they are finite; without it Lean's junk value 0 for a non-integrable integrand would change the hypothesis
--   - encoding: (B4) E[F_n(t)²] and exp(∑ λ_ℓ δ_ℓ(t)²) → ∫⁻ |F_n(t)|² (ENNReal limsup) and exp(∑' λ_ℓ |δ_ℓ(t)|²); reason: F_n(t) ≥ 0 a.s. by (B0), and δ_ℓ(t) is real for t ∈ I under (B0) and (B2) (p. 20), so the squares equal the squared moduli
--   - encoding: ∑_{ℓ≥1} λ_ℓ δ_ℓ(t)² < ∞ → Summable (λ_ℓ |δ_ℓ(t)|²); reason: δ_ℓ(t) is real under (B0) and (B2) (p. 20)
--   - encoding: →d in ℂ × ℤ_{≥0}^m → E[φ(F_n(t), X_{1..m,n})] → E[φ(W(t), Z_{1..m})] for every bounded continuous φ : ℂ × (Fin m → ℕ) → ℝ; reason: definition of convergence in distribution (p. 17)
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 20, Theorem 3.6 (cited from [Jan95, Theorem 1 and Lemma 1])

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open scoped ComplexOrder
open MeasureTheory ProbabilityTheory Filter Topology

namespace ZeroFreeRRG.Hardcore

/-- **Theorem 3.6** (real-line small subgraph conditioning [Jan95]; p. 20). In the setting of
Theorem 3.2, fix `t ∈ I` and suppose `Y_n(t) ≥ 0` almost surely, `0 < A_n(t) = E[Y_n(t)] < ∞` for
all sufficiently large `n`, (B1)–(B2) and (B4) hold at `t`, and `∑_{ℓ ≥ 1} λ_ℓ δ_ℓ(t)² < ∞`. Then for
every `m ≥ 1`, `(F_n(t), X_{1,n}, …, X_{m,n}) →d (W(t), Z_1, …, Z_m)`: `E[φ(F_n(t), X_{1..m,n})] →
E[φ(W(t), Z_{1..m})]` for every bounded continuous `φ : ℂ × ℕ^m → ℝ`. -/
theorem theorem_3_6 (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (a b : ℝ) (hab : a < b)
    (hI : ∀ s ∈ Set.Ioo a b, (s : ℂ) ∈ D)
    {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (P : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (P n)] (Y : ∀ n, Ωs n → ℂ → ℂ) (X : ∀ n, ℕ → Ωs n → ℕ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (Z : ℕ → Ω₀ → ℕ) (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ)
    (hY : ∀ n, IsRandomHol D (Y n)) (hX : ∀ n i, Measurable (X n i))
    (hlam : ∀ i, 0 < lam i) (hδ : ∀ i, DifferentiableOn ℂ (δ i) D)
    (hZ : IsIndepPoisson P₀ Z lam)
    (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hpos : ∀ n, ∀ᵐ ω ∂(P n), (0 : ℂ) ≤ Y n ω t)
    (hA : ∀ᶠ n in atTop, Integrable (fun ω => Y n ω t) (P n) ∧ (0 : ℂ) < meanFn (P n) (Y n) t)
    (hB1 : CondB1 P X P₀ Z) (hB2 : CondB2At P Y X lam δ t) (hB4 : CondB4At P Y lam δ t)
    (hsum : Summable (fun i => lam i * ‖δ i t‖ ^ 2)) :
    ∀ k : ℕ, 1 ≤ k → ∀ φ : ℂ × (Fin k → ℕ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (normalizedFn (P n) (Y n) ω t, fun i : Fin k => X n i ω) ∂(P n))
        atTop (𝓝 (∫ ω, φ (Wlim lam δ Z ω t, fun i : Fin k => Z i ω) ∂P₀)) := by sorry

end ZeroFreeRRG.Hardcore
