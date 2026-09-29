-- Prove2me | Definitions.Def_MachineLearning_BonferroniMarginals_Core
-- name    : MachineLearning_BonferroniMarginals_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:57.678609+00:00
-- url     : https://prove2.me/theorems/4295ccbf-2462-4150-b4e8-6f1f5342d7e1
-- title:
--   Aether Catalog definitions — MachineLearning_BonferroniMarginals_Core
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BonferroniMarginals.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BonferroniMarginals/Core.lean by skeleton subtraction
import Mathlib

/-!
# The Bonferroni machinery: multiplicity calculus for arbitrary finite families

This file builds, from scratch and for an *arbitrary* finite family
`A : ι → Finset Ω` indexed by a finite set `I : Finset ι`, the exact
book-keeping that underlies every Bonferroni-type inequality.

The organising object is the **multiplicity** (or *degree*, or *coverage
count*) function
`mult I A x = #{i ∈ I | x ∈ A i}`.
All first- and second-order *marginals* of the family are moments of `mult`
on the cover `⋃ i ∈ I, A i`:

* `sum_mult_eq_sum_card` : `∑ₓ mult x = ∑ᵢ |Aᵢ|`  (first marginal moment)
* `sum_mult_sq_eq_sum_prod` : `∑ₓ (mult x)² = ∑_{(i,j)} |Aᵢ ∩ Aⱼ|` (second)
* `sum_offDiag_eq` : the off-diagonal part is `∑ₓ mult x * (mult x - 1)`.

From these two identities the whole machinery follows:

* `card_sum_le_card_biUnion_add_offDiag` — the **second Bonferroni inequality**
  in its off-diagonal (unordered-pair-free) form.
* `card_doubleCollision_mul_le` — the **double-collision bound**: twice the
  number of points covered at least twice is at most the pairwise-overlap mass.
* `sq_sum_card_le_card_cover_mul_sum_prod` — the **Cauchy–Schwarz upgrade**
  `(∑ᵢ |Aᵢ|)² ≤ |cover| · ∑_{(i,j)} |Aᵢ ∩ Aⱼ|`, which is strictly stronger than
  Bonferroni whenever the family is far from a partition.

Machine-learning reading: `Ω` is a finite sample space, `A i` the set of samples
on which hypothesis `i` fails (its *bad event*), `|A i|` the first marginal,
`|A i ∩ A j|` the second.  `mult` is the number of ensemble members that fail
at a given sample, `cover` is the set of samples on which the ensemble is not
unanimously correct, and `doubleCollision` is the set of samples where the
failures are *correlated*.
-/

namespace BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## The multiplicity function -/

/-- `mult I A x` is the number of members of the family that contain `x`:
the *coverage multiplicity* of the point `x`. -/
def mult (I : Finset ι) (A : ι → Finset Ω) (x : Ω) : ℕ :=
  (I.filter (fun i => x ∈ A i)).card

/-- The union (cover) of the family. -/
def cover (I : Finset ι) (A : ι → Finset Ω) : Finset Ω := I.biUnion A

/-- The set of points covered at least twice — where two members *collide*. -/
def doubleCollision (I : Finset ι) (A : ι → Finset Ω) : Finset Ω :=
  (cover I A).filter (fun x => 2 ≤ mult I A x)






/-! ## The two moment identities -/







/-! ## The Bonferroni machinery -/




/-! ## The Cauchy–Schwarz upgrade

The Bonferroni inequality uses the pointwise bound `2d ≤ 1 + d²`.  Summing the
*sharp* Cauchy–Schwarz inequality instead gives a bound that is strictly
stronger for families that are far from a partition. -/



end BonferroniMarginals


