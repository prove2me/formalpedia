-- Prove2me | Definitions.Def_MachineLearning_TotalVariation_Testing
-- name    : MachineLearning_TotalVariation_Testing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:13:24.947675+00:00
-- url     : https://prove2.me/theorems/f4fdefa1-f0d2-4b9b-952b-d0a12a15af18
-- title:
--   Aether Catalog definitions — MachineLearning_TotalVariation_Testing
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TotalVariation.Testing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TotalVariation/Testing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Operational consequences of the sharp total-variation normalization

`MachineLearning.TotalVariation.EventSup` proved the factor-`1/2` characterization

`d_TV(p, q) = max_{A} (p(A) − q(A))`.

Here we cash it in.  Three classical pillars of statistical learning theory are
derived, each of them *tight* precisely because the normalization is the sharp
one:

1. **Le Cam's two-point bound.**  For the uniform-prior binary testing problem
   `p` vs `q`, the Bayes error of the best test is exactly `(1 − d_TV)/2`
   (`isLeast_bayesError`).  With the crude `ℓ¹` normalization one would only get
   the vacuous `(1 − ‖p − q‖₁)/2`, which is negative as soon as `‖p − q‖₁ > 1`.
2. **Data processing.**  Post-processing by an arbitrary stochastic channel — in
   particular by any deterministic feature map / statistic — cannot increase
   total variation (`tvDist_channel_le`, `tvDist_map_le`).
3. **Tensorization and sample complexity.**  `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`
   (`tvDist_powLaw_le`), so a learner needs `n ≳ 1/d_TV` i.i.d. samples before it
   can tell the two sources apart at all (`bayesError_powLaw_ge`).

## Main results

* `bayesError_eq_half_one_add_eventGap`, `isLeast_bayesError`,
  `bayesError_ge_half_one_sub_tvDist` — Le Cam;
* `tvDist_channel_le`, `tvDist_map_le` — the data-processing inequality;
* `tvDist_prodLaw_le` — two-factor tensorization (hybrid argument);
* `tvDist_powLaw_le` — the `n`-sample bound by induction;
* `bayesError_powLaw_ge` — the resulting sample-complexity lower bound.

## Application keywords

Le Cam method, hypothesis testing, data processing inequality, tensorization,
sample complexity, indistinguishability, hybrid argument
-/


open Finset

namespace UniversalRedundancy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ## Le Cam's two-point bound -/

open Classical in
/-- Average error probability of the Boolean test `f` in the uniform-prior
binary testing problem "`p` versus `q`", where the output `true` means
"the sample came from `q`". -/
noncomputable def bayesError (p q : X → ℝ) (f : X → Bool) : ℝ :=
  ((∑ x ∈ univ.filter fun x => f x = true, p x)
    + ∑ x ∈ univ.filter fun x => f x = false, q x) / 2




/-! ## The data-processing inequality -/

/-- Push-forward of the law `p` through the stochastic channel `K`. -/
def channelPush (p : X → ℝ) (K : X → Y → ℝ) : Y → ℝ := fun y => ∑ x, p x * K x y




/-! ## Tensorization -/

/-- Product law on `X × Y`. -/
def prodLaw (p : X → ℝ) (r : Y → ℝ) : X × Y → ℝ := fun z => p z.1 * r z.2



/-! ## `n` i.i.d. samples -/

/-- The `n`-fold product law: the law of `n` i.i.d. samples from `p`. -/
def powLaw (p : X → ℝ) (n : ℕ) : (Fin n → X) → ℝ := fun v => ∏ i, p (v i)







end UniversalRedundancy


