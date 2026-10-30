-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.sector_bound_with_divergence_on
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:19:19.6192+00:00
-- url     : https://prove2.me/submissions/b591a656-9e60-4d44-8430-b2c0fd83cba0

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

noncomputable section

open Finset

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
theorem solution
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
    SectorBound aAnti aSym ((Real.sqrt 8 * Real.sqrt B * Γ * L + Δ) / p) := by
  classical
  intro f g
  set Ef := edgeEnergyOn Ed f with hEf
  set Eg := edgeEnergyOn Ed g with hEg
  have hEf_nonneg : 0 ≤ Ef := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hEg_nonneg : 0 ≤ Eg := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  set C : ℝ := Real.sqrt 8 * Real.sqrt B * Γ * L with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hCsq : C ^ 2 = 8 * B * Γ ^ 2 * L ^ 2 := by
    rw [hCdef, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sq_sqrt hBnn]
  -- abbreviations for the two edge functions in the cut term
  set H : ℤ → ℝ := fun e => Hcut I J f e with hH'
  set G : ℤ → ℝ := fun e => grad g e with hG'
  -- (1) cut term:  |∑_{e∈E} H·G| ≤ C·√Ef·√Eg
  have hGsub : (∑ e ∈ E, (G e) ^ 2) ≤ Eg := by
    rw [hEg, edgeEnergyOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg hEsub (fun e _ _ => sq_nonneg _)
  have hcs : (∑ e ∈ E, H e * G e) ^ 2 ≤ (∑ e ∈ E, (H e) ^ 2) * (∑ e ∈ E, (G e) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq E H G
  have hHf : (∑ e ∈ E, (H e) ^ 2) ≤ 8 * B * Γ ^ 2 * L ^ 2 * Ef := hH f
  have hHsum_nonneg : 0 ≤ ∑ e ∈ E, (H e) ^ 2 := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hGsum_nonneg : 0 ≤ ∑ e ∈ E, (G e) ^ 2 := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hcut_sq : (∑ e ∈ E, H e * G e) ^ 2 ≤ (C * Real.sqrt Ef * Real.sqrt Eg) ^ 2 := by
    calc (∑ e ∈ E, H e * G e) ^ 2
          ≤ (∑ e ∈ E, (H e) ^ 2) * (∑ e ∈ E, (G e) ^ 2) := hcs
      _ ≤ (8 * B * Γ ^ 2 * L ^ 2 * Ef) * Eg :=
            mul_le_mul hHf hGsub hGsum_nonneg (le_trans hHsum_nonneg hHf)
      _ = (C * Real.sqrt Ef * Real.sqrt Eg) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hEf_nonneg, Real.sq_sqrt hEg_nonneg, hCsq]
  have hcut_rhs_nonneg : 0 ≤ C * Real.sqrt Ef * Real.sqrt Eg := by positivity
  have hcut : |∑ e ∈ E, H e * G e| ≤ C * Real.sqrt Ef * Real.sqrt Eg := by
    apply (sq_le_sq₀ (abs_nonneg _) hcut_rhs_nonneg).mp
    rw [sq_abs]
    exact hcut_sq
  -- triangle inequality |x - y| ≤ |x| + |y| (robust to Mathlib renamings)
  have htri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    rw [sub_eq_add_neg]
    exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
  -- (2) divergence term:  |−½∑ D·f·g| ≤ Δ·√Ef·√Eg
  have hdiv : |(- (1 / 2 : ℝ)) * ∑ x ∈ I, D x * f x * g x|
      ≤ Δ * Real.sqrt Ef * Real.sqrt Eg := hD f g
  -- (3) combine:  |aAnti| ≤ (Δ + C)·√Ef·√Eg
  have hcombine : |aAnti f g| ≤ (Δ + C) * (Real.sqrt Ef * Real.sqrt Eg) := by
    rw [hanti f g]
    calc |(- (1 / 2 : ℝ)) * (∑ x ∈ I, D x * f x * g x) - ∑ e ∈ E, H e * G e|
          ≤ |(- (1 / 2 : ℝ)) * (∑ x ∈ I, D x * f x * g x)| + |∑ e ∈ E, H e * G e| :=
            htri _ _
      _ ≤ Δ * Real.sqrt Ef * Real.sqrt Eg + C * Real.sqrt Ef * Real.sqrt Eg :=
            add_le_add hdiv hcut
      _ = (Δ + C) * (Real.sqrt Ef * Real.sqrt Eg) := by ring
  -- (4) ellipticity:  √Ef·√Eg ≤ √(aSym f f)·√(aSym g g)/p
  have hAf_nonneg : 0 ≤ aSym f f := hsym_nonneg f
  have hAg_nonneg : 0 ≤ aSym g g := hsym_nonneg g
  have hEf_le : Ef ≤ aSym f f / p := by rw [le_div_iff₀ hp]; nlinarith [helliptic f]
  have hEg_le : Eg ≤ aSym g g / p := by rw [le_div_iff₀ hp]; nlinarith [helliptic g]
  have hprod : Ef * Eg ≤ (aSym f f * aSym g g) / p ^ 2 := by
    have h1 : Ef * Eg ≤ (aSym f f / p) * (aSym g g / p) :=
      mul_le_mul hEf_le hEg_le hEg_nonneg (by positivity)
    calc Ef * Eg ≤ (aSym f f / p) * (aSym g g / p) := h1
      _ = (aSym f f * aSym g g) / p ^ 2 := by ring
  have hpsq : (aSym f f * aSym g g) / p ^ 2
      = (Real.sqrt (aSym f f) * Real.sqrt (aSym g g) / p) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hAf_nonneg, Real.sq_sqrt hAg_nonneg]
  have hsqrt_prod : Real.sqrt Ef * Real.sqrt Eg
      ≤ Real.sqrt (aSym f f) * Real.sqrt (aSym g g) / p := by
    have hmul : Real.sqrt Ef * Real.sqrt Eg = Real.sqrt (Ef * Eg) :=
      (Real.sqrt_mul hEf_nonneg Eg).symm
    rw [hmul]
    calc Real.sqrt (Ef * Eg)
          ≤ Real.sqrt ((aSym f f * aSym g g) / p ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt ((Real.sqrt (aSym f f) * Real.sqrt (aSym g g) / p) ^ 2) := by rw [hpsq]
      _ = Real.sqrt (aSym f f) * Real.sqrt (aSym g g) / p :=
            Real.sqrt_sq (by positivity)
  -- (5) assemble the sector constant
  have hDC_nonneg : 0 ≤ Δ + C := by linarith
  calc |aAnti f g|
        ≤ (Δ + C) * (Real.sqrt Ef * Real.sqrt Eg) := hcombine
    _ ≤ (Δ + C) * (Real.sqrt (aSym f f) * Real.sqrt (aSym g g) / p) :=
          mul_le_mul_of_nonneg_left hsqrt_prod hDC_nonneg
    _ = (Real.sqrt 8 * Real.sqrt B * Γ * L + Δ) / p
          * Real.sqrt (aSym f f) * Real.sqrt (aSym g g) := by
          rw [hCdef]; ring
