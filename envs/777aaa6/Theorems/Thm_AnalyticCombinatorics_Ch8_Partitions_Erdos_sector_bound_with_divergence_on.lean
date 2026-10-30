-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sector_bound_with_divergence_on
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sector_bound_with_divergence_on
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:18:20.189193+00:00
-- url     : https://prove2.me/theorems/c5c71cf5-861a-44e0-b659-ef7b10b25219
-- title:
--   A conditional sector estimate retaining divergence
-- statement:
--   Fix the finite integer index and edge sets $I,E,E_d$ with $E\subseteq E_d$. Assume $B,\Gamma,L,\Delta\ge0$ and $p>0$, the full cutoff-flux energy bound, divergence bilinear estimate, exact antisymmetric-form decomposition, ellipticity and nonnegativity of the symmetric form stated below. Then the source forms satisfy $$|a_{\rm Anti}(f,g)|\le\frac{\sqrt8\sqrt B\,\Gamma L+\Delta}{p}\sqrt{a_{\rm Sym}(f,f)}\sqrt{a_{\rm Sym}(g,g)}.$$ The divergence term is retained; no stationarity premise is silently substituted.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem sector_bound_with_divergence_on
--       {I E Ed : Finset ℤ}
--       (B Γ L Δ p : ℝ)
--       (J : ℤ → ℤ → ℝ) (D : ℤ → ℝ)
--       (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ)
--       (hBnn : 0 ≤ B) (hΓnn : 0 ≤ Γ) (hLnn : 0 ≤ L) (hΔnn : 0 ≤ Δ) (hp : 0 < p)
--       (hEsub : E ⊆ Ed)
--       (hH : ∀ f, ∑ e ∈ E, (Hcut I J f e) ^ 2
--               ≤ 8 * B * Γ ^ 2 * L ^ 2 * edgeEnergyOn Ed f)
--       (hD : ∀ f g, |(- (1 / 2 : ℝ)) * ∑ x ∈ I, D x * f x * g x|
--               ≤ Δ * Real.sqrt (edgeEnergyOn Ed f) * Real.sqrt (edgeEnergyOn Ed g))
--       (hanti : ∀ f g, aAnti f g
--               = (- (1 / 2 : ℝ)) * (∑ x ∈ I, D x * f x * g x)
--                 - ∑ e ∈ E, Hcut I J f e * grad g e)
--       (helliptic : ∀ f, p * edgeEnergyOn Ed f ≤ aSym f f)
--       (hsym_nonneg : ∀ f, 0 ≤ aSym f f) :
--       SectorBound aAnti aSym ((Real.sqrt 8 * Real.sqrt B * Γ * L + Δ) / p)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SectorBoundDivergence.lean#L34. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SectorBound
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Sector bound carrying a divergence term

`sector_bound_from_Hcut_on` (SectorBound) consumes the *divergence-free* cut identity
`aAnti = − ∑ Hcut·grad`, valid only when the reference measure is stationary (so `divJ ≡ 0`).  For a
finite/killed window the windowed chain leaks mass at the boundary, so the exact cut identity carries
an extra divergence term

  `aAnti f g = −½ ∑_{x∈I} divJ(x)·f x·g x − ∑_{e∈E} Hcut·grad g e`   (`aAnti_eq_div_plus_Hcut`).

This file adds the abstract sector bound that keeps that divergence term, bounding it by an additional
`Δ·√(E f)·√(E g)` input.  The resulting sector constant is `(√8·√B·Γ·L + Δ)/p`.  It is fully abstract
in `aAnti, aSym, J, D` — reusable both for the 1-D residual chain (`I = Icc a b`, `D = divJ I (JresZ p)`,
`Δ = (escaped mass)·L`) and, after the pair/`D`-projection generalization, at the pair level.

The proof mirrors `sector_bound_from_Hcut_on` but uses the *linear* triangle inequality
`|aAnti| ≤ |div term| + |cut term|` instead of squaring, since the two-term sum has no clean square.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sector_bound_with_divergence_on
    {I E Ed : Finset ℤ}
    (B Γ L Δ p : ℝ)
    (J : ℤ → ℤ → ℝ) (D : ℤ → ℝ)
    (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ)
    (hBnn : 0 ≤ B) (hΓnn : 0 ≤ Γ) (hLnn : 0 ≤ L) (hΔnn : 0 ≤ Δ) (hp : 0 < p)
    (hEsub : E ⊆ Ed)
    (hH : ∀ f, ∑ e ∈ E, (Hcut I J f e) ^ 2
            ≤ 8 * B * Γ ^ 2 * L ^ 2 * edgeEnergyOn Ed f)
    (hD : ∀ f g, |(- (1 / 2 : ℝ)) * ∑ x ∈ I, D x * f x * g x|
            ≤ Δ * Real.sqrt (edgeEnergyOn Ed f) * Real.sqrt (edgeEnergyOn Ed g))
    (hanti : ∀ f g, aAnti f g
            = (- (1 / 2 : ℝ)) * (∑ x ∈ I, D x * f x * g x)
              - ∑ e ∈ E, Hcut I J f e * grad g e)
    (helliptic : ∀ f, p * edgeEnergyOn Ed f ≤ aSym f f)
    (hsym_nonneg : ∀ f, 0 ≤ aSym f f) :
    SectorBound aAnti aSym ((Real.sqrt 8 * Real.sqrt B * Γ * L + Δ) / p) := by sorry
