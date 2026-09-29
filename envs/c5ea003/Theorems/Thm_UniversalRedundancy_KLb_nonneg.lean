-- Prove2me | Theorems.Thm_UniversalRedundancy_KLb_nonneg
-- name    : UniversalRedundancy.KLb_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:54:41.35875+00:00
-- url     : https://prove2.me/theorems/96da467d-7a1d-43e1-91cc-33a5683975b2
-- title:
--   Gibbs' inequality.
-- statement:
--   **Gibbs' inequality.**  Relative entropy between probability vectors with
--   positive entries is non-negative.
--
--   ```lean
--   theorem UniversalRedundancy.KLb_nonneg(p q : X → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
--       (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) : 0 ≤ KLb p q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Capacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Capacity.lean#L63

-- Thm stub generated from MachineLearning/UniversalRedundancy/Capacity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
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

open UniversalRedundancy

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ]

theorem UniversalRedundancy.KLb_nonneg(p q : X → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) : 0 ≤ KLb p q := by sorry
