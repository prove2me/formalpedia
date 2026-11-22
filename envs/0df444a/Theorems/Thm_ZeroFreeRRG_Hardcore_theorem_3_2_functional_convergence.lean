-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_3_2_functional_convergence
-- name    : ZeroFreeRRG.Hardcore.theorem_3_2_functional_convergence
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:45:37.968077+00:00
-- url     : https://prove2.me/theorems/462a921e-92fa-47fa-a714-fafaf212ce47
-- title:
--   RSSC: functional convergence from tightness and real-line identification
-- statement:
--   This is the functional-distributional assertion in the proof of reinforced small subgraph conditioning. Let $D\subseteq\mathbb C$ be open and connected, let $I=(a,b)$ be a nonempty real interval contained in $D$, and suppose the normalized random holomorphic functions $F_n=Y_n/A_n$, the cycle counts $X_{\ell,n}$, and the independent Poisson variables $Z_\ell$ satisfy hypotheses (B0)–(B5) of Theorem 3.2. Assume also that the partial products $W_N$ converge locally uniformly on $D$ to $W$, almost surely.
--
--   Then
--   $$
--   \big(F_n,(X_{\ell,n})_{\ell\ge1}\big)\xrightarrow{d}
--   \big(W,(Z_\ell)_{\ell\ge1}\big)
--   \qquad\text{in }H(D)\times\mathbb Z_{\ge0}^{\mathbb Z_{\ge1}}.
--   $$
--   Equivalently, $\mathbb E[\varphi(F_n,X_n)]\to\mathbb E[\varphi(W,Z)]$ for every bounded continuous real-valued test function $\varphi$ on the product space.
--
--   This isolates the identification of all subsequential limits in Theorem 3.2. Its intended inputs are Lemmas 3.4 and 3.5 and Theorem 3.6.
--
--   **Formalization Note.** Holomorphic functions are represented in `HFun D`, and convergence in distribution is expressed by convergence of Bochner integrals of bounded continuous test functions. The index $i\in\mathbb N$ represents $\ell=i+1$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 22, proof of Theorem 3.2, first paragraph (using Lemma 3.4, Lemma 3.5, Theorem 3.6, Prokhorov's theorem, and Proposition 2.8)

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology
open ZeroFreeRRG.Hardcore

/-- The functional-distributional part of Theorem 3.2, proved by tightness, Prokhorov's theorem,
real-line small subgraph conditioning, and the identity theorem (p. 22, first paragraph). -/
theorem ZeroFreeRRG.Hardcore.theorem_3_2_functional_convergence (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D)
    (a b : ℝ) (hab : a < b) (hI : ∀ t ∈ Set.Ioo a b, (t : ℂ) ∈ D)
    {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (P : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (P n)] (Y : ∀ n, Ωs n → ℂ → ℂ) (X : ∀ n, ℕ → Ωs n → ℕ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (Z : ℕ → Ω₀ → ℕ) (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ)
    (hY : ∀ n, IsRandomHol D (Y n)) (hX : ∀ n i, Measurable (X n i))
    (hlam : ∀ i, 0 < lam i) (hδ : ∀ i, DifferentiableOn ℂ (δ i) D)
    (hZ : IsIndepPoisson P₀ Z lam)
    (hB0 : CondB0 P Y D (Set.Ioo a b)) (hB1 : CondB1 P X P₀ Z)
    (hB2 : ∀ t ∈ Set.Ioo a b, CondB2At P Y X lam δ t) (hB3 : CondB3 lam δ D)
    (hB4 : ∀ t ∈ Set.Ioo a b, CondB4At P Y lam δ t) (hB5 : CondB5 P Y D)
    (hW : ∀ᵐ ω ∂P₀, TendstoLocallyUniformlyOn (fun N => Wpartial lam δ Z N ω)
      (Wlim lam δ Z ω) atTop D) :
    ∀ φ : HFun D × (ℕ → ℕ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (toH D (normalizedFn (P n) (Y n) ω), fun i => X n i ω) ∂(P n))
        atTop (𝓝 (∫ ω, φ (toH D (Wlim lam δ Z ω), fun i => Z i ω) ∂P₀)) := by sorry
