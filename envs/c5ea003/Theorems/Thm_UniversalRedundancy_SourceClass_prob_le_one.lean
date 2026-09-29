-- Prove2me | Theorems.Thm_UniversalRedundancy_SourceClass_prob_le_one
-- name    : UniversalRedundancy.SourceClass.prob_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:54:01.667566+00:00
-- url     : https://prove2.me/theorems/2efccfd6-a775-4a2f-b669-152c88981b5f
-- title:
--   Prob le one
-- statement:
--   Formal statement of `UniversalRedundancy.SourceClass.prob_le_one` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem UniversalRedundancy.SourceClass.prob_le_one(θ : Θ) (x : X) : S.prob θ x ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Core.lean#L65

-- Thm stub generated from MachineLearning/UniversalRedundancy/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
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

open UniversalRedundancy


open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)

theorem UniversalRedundancy.SourceClass.prob_le_one(θ : Θ) (x : X) : S.prob θ x ≤ 1 := by sorry
