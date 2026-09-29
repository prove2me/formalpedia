-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Core
-- name    : MachineLearning_UniversalRedundancy_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:00:09.47132+00:00
-- url     : https://prove2.me/theorems/11c65e85-b2d5-476e-aecb-3238f084db05
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Core
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Core.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality I: Shtarkov's exact minimax redundancy

Research thread *Compression Beyond the Pigeonhole Bound*, Phase A, Question 1:
**one shared decompressor must serve all inputs**.  The counting core
(`MachineLearning.PRNGCompressionCore`) shows that no code shortens all inputs.
This file asks the quantitative refinement: if the data is known to come from
*some* member of a class of sources `{p_θ}_{θ ∈ Θ}`, how many bits does a single
universal code lose against the code tailored to the true `θ`?

## Central Idea

For a coding distribution `q` the pointwise redundancy at message `x` under
source `θ` is `log₂ (p_θ x / q x)`.  The worst case over `x` and `θ` is governed
by the **Shtarkov sum**

`Cₛ = ∑ₓ sup_θ p_θ x`,

and the optimum is attained by the *normalized maximum likelihood* distribution
`nml x = (sup_θ p_θ x) / Cₛ`.  Both directions are proved here, in a
division-free multiplicative form that needs no positivity assumptions, and in
logarithmic (bit) form under the natural positivity hypotheses.

## Main Results

* `maxLik`, `shtarkovSum`, `nml` — the basic objects
* `one_le_shtarkovSum`, `shtarkovSum_le_card` — `1 ≤ Cₛ ≤ #Θ`
* `prob_le_shtarkovSum_mul_nml` — achievability: NML pays at most `log₂ Cₛ`
  uniformly over messages *and* sources
* `exists_subprob_ratio_ge` — converse: *every* coding sub-probability `q`
  suffers redundancy at least `log₂ Cₛ` somewhere
* `shtarkov_minimax` — the two combined: the minimax pointwise redundancy is
  exactly `log₂ Cₛ`
* `kraft_converse` — code-length form: every code obeying Kraft has a message on
  which it is `log₂ Cₛ` bits worse than the ideal code for the true source
* `nmlCodeLength_le` — a matching universal code within one bit
* `shtarkovSum_eq_card_of_disjoint_supports` — for classes of mutually singular
  sources the price of universality is exactly `log₂ #Θ`: nothing can be shared

## Application Keywords

universal compression, minimax redundancy, Shtarkov sum, normalized maximum
likelihood, Kraft inequality, price of universality
-/


open Finset Real

namespace UniversalRedundancy

/-- A parametric class of sources on a finite message space `X`, indexed by `Θ`. -/
structure SourceClass (X : Type*) [Fintype X] (Θ : Type*) where
  /-- probability of message `x` under source `θ` -/
  prob : Θ → X → ℝ
  nonneg : ∀ θ x, 0 ≤ prob θ x
  sum_one : ∀ θ, ∑ x, prob θ x = 1

namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)



/-- The maximum-likelihood envelope of the class: `sup_θ p_θ x`. -/
noncomputable def maxLik (x : X) : ℝ := ⨆ θ, S.prob θ x






/-- **Shtarkov sum** of the class: `Cₛ = ∑ₓ sup_θ p_θ x`. -/
noncomputable def shtarkovSum : ℝ := ∑ x, S.maxLik x




/-- The **normalized maximum likelihood** (Shtarkov) coding distribution. -/
noncomputable def nml (x : X) : ℝ := S.maxLik x / S.shtarkovSum







/-! ## Code-length form

A code with lengths `ℓ : X → ℕ` is *Kraft compliant* if `∑ₓ 2 ^ (-ℓ x) ≤ 1`;
this is exactly the condition for a prefix-free binary code to exist.  The ideal
code for a known source `θ` spends `log₂ (1 / p_θ x)` bits on `x`. -/

/-- Kraft compliance of a length function. -/
def Kraft (ℓ : X → ℕ) : Prop := ∑ x, (2 : ℝ) ^ (-(ℓ x : ℤ)) ≤ 1




/-- The universal NML code: `ℓ*(x) = ⌈log₂ (1 / nml x)⌉`. -/
noncomputable def nmlCodeLength (x : X) : ℕ := ⌈logb 2 (1 / S.nml x)⌉₊




/-! ## The extreme case: mutually singular sources

If distinct sources live on disjoint supports, nothing can be shared and the
price of universality is the full `log₂ #Θ` bits. -/


end SourceClass

end UniversalRedundancy


