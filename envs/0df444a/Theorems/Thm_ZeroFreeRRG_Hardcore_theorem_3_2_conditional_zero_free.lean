-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_3_2_conditional_zero_free
-- name    : ZeroFreeRRG.Hardcore.theorem_3_2_conditional_zero_free
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:47:42.079179+00:00
-- url     : https://prove2.me/theorems/08ef4550-5885-49a2-a114-498b0006b6b4
-- title:
--   RSSC: conditional zero-freeness from functional convergence
-- statement:
--   This is the conditional zero-freeness conclusion in reinforced small subgraph conditioning. In the setting of Theorem 3.2, assume the functional distributional convergence
--   $$
--   (F_n,X_n)\xrightarrow{d}(W,Z)
--   $$
--   and suppose $1+\delta_\ell$ is nowhere zero on $D$ for every $\ell\ge3$. Assume further that, conditionally on $Z_1=Z_2=0$, the limiting function $W$ is almost surely nowhere zero on $D$.
--
--   Then for every compact $K\subset D$,
--   $$
--   \Pr\!\left[Y_n\text{ has no zero on }K\ \middle|\ X_{1,n}=X_{2,n}=0\right]
--   \longrightarrow1.
--   $$
--   This is precisely the final assertion of Theorem 3.2, separated from the functional-limit argument so that the analytic and probabilistic steps can be developed independently.
--
--   **Formalization Note.** The displayed conditional probability is represented by `ProbabilityTheory.cond`; the index $i\in\mathbb N$ represents $\ell=i+1$, so the conditioning event is `X n 0 = 0` and `X n 1 = 0`.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 22, proof of Theorem 3.2, second paragraph (Portmanteau argument)

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RSSC

open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology
open ZeroFreeRRG.Hardcore

/-- The conditional zero-freeness consequence of functional convergence and nonvanishing of W,
proved by the Portmanteau theorem (p. 22, second paragraph). -/
theorem ZeroFreeRRG.Hardcore.theorem_3_2_conditional_zero_free (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D)
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
    (hFn : ∀ φ : HFun D × (ℕ → ℕ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (toH D (normalizedFn (P n) (Y n) ω), fun i => X n i ω) ∂(P n))
        atTop (𝓝 (∫ ω, φ (toH D (Wlim lam δ Z ω), fun i => Z i ω) ∂P₀)))
    (hnz : ∀ i, 2 ≤ i → ∀ z ∈ D, 1 + δ i z ≠ 0)
    (hWnz : ∀ᵐ ω ∂(P₀[|{ω | Z 0 ω = 0 ∧ Z 1 ω = 0}]),
      ∀ z ∈ D, Wlim lam δ Z ω z ≠ 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ D →
      Tendsto (fun n => (P n)[|{ω | X n 0 ω = 0 ∧ X n 1 ω = 0}] {ω | ∀ z ∈ K, Y n ω z ≠ 0})
        atTop (𝓝 1) := by sorry
