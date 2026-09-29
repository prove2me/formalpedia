-- Prove2me | Definitions.Def_Bridges_TropicalInformationBottleneckDuality
-- name    : Bridges_TropicalInformationBottleneckDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:29.396617+00:00
-- url     : https://prove2.me/theorems/62110772-87da-40e8-8977-70992fb31603
-- title:
--   Aether Catalog definitions — Bridges_TropicalInformationBottleneckDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalInformationBottleneckDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalInformationBottleneckDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalBottleneck

variable {ι R : Type*}

/-! ## Section A: Core Definitions -/

/-- The tropical bottleneck objective for a single observer at parameter β:
    the "affine tropical functional" `cap(i) + β * dist(i)`. -/
def objective [Add R] [Mul R] (cap dist : ι → R) (β : R) (i : ι) : R :=
  cap i + β * dist i

/-- The bottleneck value function: minimum of objectives over the observer set.
    This is the tropical analogue of the rate-distortion function. -/
def bottleneckVal [LinearOrder R] [Add R] [Mul R] (Obs : Finset ι) (cap dist : ι → R)
    (hne : Obs.Nonempty) (β : R) : R :=
  Obs.inf' hne (fun i => objective cap dist β i)

/-- The **certified rate region**: upward closure of the operadic spectrum. -/
def certifiedRateRegion [Preorder R] (Obs : Finset ι) (cap dist : ι → R) :
    Set (R × R) :=
  { p | ∃ i ∈ Obs, cap i ≤ p.1 ∧ dist i ≤ p.2 }

/-! ## Section B: Bottleneck Realization — Core Theorems -/





/-! ## Section C: Scalarization Monotonicity -/



/-! ## Section D: Main Duality Theorem -/


/-! ## Section E: Certified Rate Region -/



/-! ## Section F: Computability -/


/-! ## Section G: Breakpoint Analysis -/


end TropicalBottleneck

end


