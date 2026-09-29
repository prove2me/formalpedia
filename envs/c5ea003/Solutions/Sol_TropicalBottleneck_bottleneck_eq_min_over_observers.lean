-- Prove2me | solution 1 for TropicalBottleneck.bottleneck_eq_min_over_observers
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:59.561971+00:00
-- url     : https://prove2.me/submissions/7a87db04-b7e4-482a-883b-3ddecf68ef6d

-- Sol generated from Bridges/TropicalInformationBottleneckDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalInformationBottleneckDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Information Bottleneck Duality via Closure Capacities and Neural Operad Rate Regions

This file establishes a rigorous min-plus information bottleneck theorem that unifies:

1. **Closure-theoretic semantics** of representation (closure capacity as primal resource),
2. **Operadic compositional complexity** of neural architectures (finite observer spectra),
3. **Rate–distortion duality** in tropical algebra (Legendre/Fenchel conjugacy).

## Main Results

* `bottleneck_realized_by_observer` — The bottleneck value is realized by some observer.
* `bottleneck_piecewise_affine` — The bottleneck is piecewise affine.
* `slopes_subset_distortion_spectrum` — Slopes lie in the finite distortion spectrum.
* `bottleneck_eq_min_over_observers` — Main duality: observer minimum = admissible infimum.
* `admissible_pair_in_rate_region` — Certified rate region characterization.
* `objective_mono_of_dominates` — Monotone scalarization under domination.
* `certifiedRateRegion_upward_closed` — Rate region is upward closed.
* `exists_extreme_observer_minimizer` — Extreme observer realizes optimum.
* `finite_breakpoints` — Finite breakpoint set.

## Bridge Connections

* Connects to `LawvereRateDistortionDuality.lean`: observer sufficiency generalizes
  the weak duality principle `prime_capacity_le_rate_distortion` to a finite attainment
  result via the monotone scalarization mechanism.
* Connects to `OperadicDeepLearning/Foundations.lean`: the finite observer spectrum
  arises from canonical factorizations of the neural operad generators, and extreme
  observer factors correspond to Pareto-optimal architectures.

## References

* Shannon, C.E. — Coding theorems for a discrete source with a fidelity criterion (1959)
* Litvinov, G.L. — Maslov dequantization, idempotent and tropical mathematics (2007)
* Lawvere, F.W. — Metric spaces, generalized logic, and closed categories (1973)
-/


open Finset

noncomputable section

open TropicalBottleneck

variable {ι R : Type*}

/-! ## Section A: Core Definitions -/




/-! ## Section B: Bottleneck Realization — Core Theorems -/





/-! ## Section C: Scalarization Monotonicity -/

/-- Arithmetic helper: a + β * b ≤ c + β * d when a ≤ c, b ≤ d, and β ≥ 0. -/
private lemma add_mul_le_add_mul [LinearOrder R] [Semiring R] [IsOrderedRing R]
    {a b c d β : R} (hab : a ≤ c) (hcd : b ≤ d) (hβ : 0 ≤ β) :
    a + β * b ≤ c + β * d :=
  add_le_add hab (mul_le_mul_of_nonneg_left hcd hβ)


/-! ## Section D: Main Duality Theorem -/


/-! ## Section E: Certified Rate Region -/



/-! ## Section F: Computability -/


/-! ## Section G: Breakpoint Analysis -/




open TropicalBottleneck in
theorem solution[ConditionallyCompleteLinearOrder R]
    [Semiring R] [IsOrderedRing R]
    (Obs : Finset ι) (cap_obs dist_obs : ι → R) (hne : Obs.Nonempty)
    (Z : Type*) (Adm : Set Z) (Cap Dist : Z → R)
    (hAdm : Adm.Nonempty)
    (hObs_adm : ∀ i ∈ Obs, ∃ z ∈ Adm, Cap z = cap_obs i ∧ Dist z = dist_obs i)
    (hSuff : ∀ z ∈ Adm, ∃ i ∈ Obs, cap_obs i ≤ Cap z ∧ dist_obs i ≤ Dist z)
    (β : R) (hβ : 0 ≤ β) :
    Obs.inf' hne (fun i => cap_obs i + β * dist_obs i) =
      sInf ((fun z => Cap z + β * Dist z) '' Adm) := by
  apply le_antisymm
  · -- Direction 1: inf' ≤ sInf (observer minimum bounds every admissible)
    apply le_csInf (hAdm.image _)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi, hci, hdi⟩ := hSuff z hz
    exact le_trans (inf'_le _ hi) (add_mul_le_add_mul hci hdi hβ)
  · -- Direction 2: sInf ≤ inf' (each observer value appears in the image)
    apply Finset.le_inf'
    intro i hi
    obtain ⟨z, hzAdm, hzCap, hzDist⟩ := hObs_adm i hi
    have hmem : Cap z + β * Dist z ∈ (fun z => Cap z + β * Dist z) '' Adm :=
      ⟨z, hzAdm, rfl⟩
    have hbdd : BddBelow ((fun z => Cap z + β * Dist z) '' Adm) := by
      use Obs.inf' hne (fun i => cap_obs i + β * dist_obs i)
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj, hcj, hdj⟩ := hSuff w hw
      exact le_trans (inf'_le _ hj) (add_mul_le_add_mul hcj hdj hβ)
    calc sInf ((fun z => Cap z + β * Dist z) '' Adm)
        ≤ Cap z + β * Dist z := csInf_le hbdd hmem
      _ = cap_obs i + β * dist_obs i := by rw [hzCap, hzDist]
