-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
-- name    : MachineLearning_UniversalRedundancy_Capacity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:33.702653+00:00
-- url     : https://prove2.me/theorems/46b05274-5a0b-4100-ac2e-5d58c93df5e8
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Capacity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Capacity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Capacity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality IV: the redundancy–capacity lower bound

Fourth instalment of the thread.  `UniversalRedundancy.Core` computed the
*worst-case* (pointwise) minimax redundancy exactly: `log₂ Cₛ`.  This file
develops the *average-case* side, which produces lower bounds that do not
depend on any single bad message: the Bayes / capacity bound.

## Central Idea

Put a prior `w` on the class.  For any coding distribution `q`,

`∑_θ w_θ · D(p_θ ‖ q) = I(w) + D(m_w ‖ q)`   (compensation identity),

where `m_w = ∑_θ w_θ p_θ` is the mixture and `I(w) = ∑_θ w_θ D(p_θ ‖ m_w)` is
the mutual information between parameter and data.  Since relative entropy is
non-negative (Gibbs), the mixture code is Bayes optimal and

`I(w) ≤ inf_q sup_θ D(p_θ ‖ q) ≤ log₂ Cₛ`.

So the *capacity* of the class is a lower bound on the average redundancy of any
universal scheme, and it never exceeds the worst-case answer of Part I.  All
statements are for strictly positive laws and priors, the regime where relative
entropy is finite and the classical theory lives.

## Main Results

* `KLb`, `mixture`, `mutualInfo`, `bayesRedundancy` — relative entropy in bits,
  the Bayes mixture, the capacity functional, and Bayes-average redundancy
* `KLb_nonneg` — Gibbs' inequality
* `compensation_identity` — the exact Bayes decomposition
* `mutualInfo_le_bayesRedundancy` — the mixture code is Bayes optimal: no code
  beats `I(w)` on average
* `exists_source_KLb_ge_mutualInfo` — minimax ≥ maximin: every coding
  distribution suffers at least `I(w)` against some source of the class
* `mutualInfo_le_logb_shtarkovSum` — capacity never exceeds the worst-case price
  `log₂ Cₛ` of Part I, tying the two theories together
* `mutualInfo_le_entropy`, `entropyb_le_logb_card` — `I(w) ≤ H(w) ≤ log₂ #Θ`:
  the price of universality is at most the cost of *naming the source*

## Application Keywords

redundancy-capacity theorem, relative entropy, Gibbs inequality, Bayes mixture
code, mutual information, universal coding
-/


open Finset Real

namespace UniversalRedundancy

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ]

/-- Relative entropy (Kullback–Leibler divergence) measured in bits. -/
noncomputable def KLb (p q : X → ℝ) : ℝ := ∑ x, p x * logb 2 (p x / q x)

/-- Shannon entropy in bits. -/
noncomputable def entropyb (p : X → ℝ) : ℝ := ∑ x, -(p x * logb 2 (p x))


/-- The Bayes mixture of the class under a prior `w`. -/
noncomputable def mixture (S : SourceClass X Θ) (w : Θ → ℝ) (x : X) : ℝ :=
  ∑ θ, w θ * S.prob θ x

/-- The mutual information (capacity functional) of a prior. -/
noncomputable def mutualInfo (S : SourceClass X Θ) (w : Θ → ℝ) : ℝ :=
  ∑ θ, w θ * KLb (S.prob θ) (mixture S w)

/-- The Bayes-average redundancy of a coding distribution `q` under prior `w`. -/
noncomputable def bayesRedundancy (S : SourceClass X Θ) (w : Θ → ℝ) (q : X → ℝ) : ℝ :=
  ∑ θ, w θ * KLb (S.prob θ) q

variable (S : SourceClass X Θ)






/-! ## Capacity never exceeds the worst-case price -/



/-! ## Capacity is at most the entropy of the prior -/



end UniversalRedundancy


