-- Prove2me | Definitions.Def_NumberTheory_RLHFLogConvexity
-- name    : NumberTheory_RLHFLogConvexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:18.176774+00:00
-- url     : https://prove2.me/theorems/78907135-7d54-4e07-a17d-5ecc0b012c7b
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFLogConvexity
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFLogConvexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFLogConvexity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# Log-convexity of the RLHF partition function

The partition function of an RLHF problem, read as a function of the *inverse* KL
coefficient `t = β⁻¹`,

```
expSum r p t = ∑_y p y · exp (r y · t),
```

is log-convex.  This file proves the midpoint form of that statement by Cauchy–Schwarz and
transports it to the free energy, giving the *harmonic annealing inequality*: the normalized
alignment value `V(β)/β` at the harmonic mean of two KL coefficients is dominated by the
average of the endpoint values.

Main results:

* `RLHF.expSum_sq_le` — midpoint log-convexity of the exponential sum;
* `RLHF.partition_eq_expSum` — the partition function at KL coefficient `β` is the
  exponential sum at inverse temperature `β⁻¹`;
* `RLHF.freeEnergy_harmonic_le` — the harmonic annealing inequality for the free energy.

The full (differential) convexity statement, together with the identification of the
curvature with the reward variance, is proved downstream in `RLHFVarianceCurvature`.
-/

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The exponential sum `∑_y p y · exp (r y · t)`: the partition function read at inverse
temperature `t`. -/
noncomputable def expSum (r p : Ω → ℝ) (t : ℝ) : ℝ := ∑ y, p y * Real.exp (r y * t)





end RLHF


