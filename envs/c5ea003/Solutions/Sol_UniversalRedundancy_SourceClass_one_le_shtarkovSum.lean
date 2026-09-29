-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.one_le_shtarkovSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:52:08.965793+00:00
-- url     : https://prove2.me/submissions/2f9f2cd0-2fe5-49ea-95c3-4d262bc5e543

-- Sol generated from MachineLearning/UniversalRedundancy/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
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




















/-! ## Code-length form

A code with lengths `ℓ : X → ℕ` is *Kraft compliant* if `∑ₓ 2 ^ (-ℓ x) ≤ 1`;
this is exactly the condition for a prefix-free binary code to exist.  The ideal
code for a known source `θ` spends `log₂ (1 / p_θ x)` bits on `x`. -/









/-! ## The extreme case: mutually singular sources

If distinct sources live on disjoint supports, nothing can be shared and the
price of universality is the full `log₂ #Θ` bits. -/




open UniversalRedundancy in
theorem solution[Nonempty Θ] : 1 ≤ S.shtarkovSum := by
  have h := S.sum_one (Classical.arbitrary Θ)
  calc (1 : ℝ) = ∑ x, S.prob (Classical.arbitrary Θ) x := h.symm
    _ ≤ ∑ x, S.maxLik x := Finset.sum_le_sum fun x _ => S.le_maxLik _ x
    _ = S.shtarkovSum := rfl
