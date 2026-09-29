-- Prove2me | Theorems.Thm_TropicalBottleneck_bottleneck_eq_min_over_observers
-- name    : TropicalBottleneck.bottleneck_eq_min_over_observers
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:20:07.889632+00:00
-- url     : https://prove2.me/theorems/89c64440-27eb-4eac-90c5-82f11fb38211
-- title:
--   Main Tropical Bottleneck Duality Theorem: Under observer sufficiency,
-- statement:
--   **Main Tropical Bottleneck Duality Theorem**: Under observer sufficiency,
--       the infimum over all admissible latents equals the minimum over observers.
--
--       `min_{i ∈ Obs}(cap_i + β * dist_i) = inf_{z ∈ Adm}(Cap(z) + β * Dist(z))`
--
--       This is the tropical information bottleneck duality: closure capacities (primal)
--       and operadic spectra (dual) yield the same bottleneck value through min-plus
--       Legendre conjugacy.
--
--       The proof follows Strategy A:
--       1. Observer sufficiency provides domination for every admissible latent.
--       2. Monotone scalarization (`add_mul_le_add_mul`) upgrades domination to objective bounds.
--       3. Realizability embeds the observer spectrum into the admissible image.
--       4. `le_antisymm` combines both directions via `le_csInf` and `csInf_le`.
--
--   ```lean
--   theorem TropicalBottleneck.bottleneck_eq_min_over_observers[ConditionallyCompleteLinearOrder R]
--       [Semiring R] [IsOrderedRing R]
--       (Obs : Finset ι) (cap_obs dist_obs : ι → R) (hne : Obs.Nonempty)
--       (Z : Type*) (Adm : Set Z) (Cap Dist : Z → R)
--       (hAdm : Adm.Nonempty)
--       (hObs_adm : ∀ i ∈ Obs, ∃ z ∈ Adm, Cap z = cap_obs i ∧ Dist z = dist_obs i)
--       (hSuff : ∀ z ∈ Adm, ∃ i ∈ Obs, cap_obs i ≤ Cap z ∧ dist_obs i ≤ Dist z)
--       (β : R) (hβ : 0 ≤ β) :
--       Obs.inf' hne (fun i => cap_obs i + β * dist_obs i) =
--         sInf ((fun z => Cap z + β * Dist z) '' Adm) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalInformationBottleneckDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalInformationBottleneckDuality.lean#L125

-- Thm stub generated from Bridges/TropicalInformationBottleneckDuality.lean
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



/-! ## Section D: Main Duality Theorem -/

theorem TropicalBottleneck.bottleneck_eq_min_over_observers[ConditionallyCompleteLinearOrder R]
    [Semiring R] [IsOrderedRing R]
    (Obs : Finset ι) (cap_obs dist_obs : ι → R) (hne : Obs.Nonempty)
    (Z : Type*) (Adm : Set Z) (Cap Dist : Z → R)
    (hAdm : Adm.Nonempty)
    (hObs_adm : ∀ i ∈ Obs, ∃ z ∈ Adm, Cap z = cap_obs i ∧ Dist z = dist_obs i)
    (hSuff : ∀ z ∈ Adm, ∃ i ∈ Obs, cap_obs i ≤ Cap z ∧ dist_obs i ≤ Dist z)
    (β : R) (hβ : 0 ≤ β) :
    Obs.inf' hne (fun i => cap_obs i + β * dist_obs i) =
      sInf ((fun z => Cap z + β * Dist z) '' Adm) := by sorry
