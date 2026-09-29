-- Prove2me | Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
-- name    : MachineLearning_BonferroniMarginals_Rigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:37:36.448705+00:00
-- url     : https://prove2.me/theorems/eba6ce69-a640-4f7e-aeac-d2f1514d8e65
-- title:
--   Aether Catalog definitions — MachineLearning_BonferroniMarginals_Rigidity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BonferroniMarginals.Rigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BonferroniMarginals/Rigidity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core

/-!
# Rigidity: exactly how much the Bonferroni machinery loses

`Core.lean` proves the two Bonferroni-type inequalities for an arbitrary finite
family.  This file identifies their **defect** exactly, and characterises the
families that make each of them an equality.  The slogan is:

> Every Bonferroni inequality is an identity plus a nonnegative *irregularity*
> functional of the multiplicity function; the inequality is tight precisely on
> the families whose irregularity vanishes.

Main results.

* `bonferroni_defect_identity` — the exact identity
  `∑ᵢ|Aᵢ| + ∑ₓ (mult x − 1)² = |cover| + ∑_{i≠j}|Aᵢ ∩ Aⱼ|`.
  The Bonferroni slack is the total squared deviation of the coverage
  multiplicity from `1`.
* `bonferroni_tight_iff_mult_one`, `bonferroni_tight_iff_pairwiseDisjoint` —
  the second Bonferroni inequality is an equality **iff** the family is pairwise
  disjoint.
* `doubleCollision_tight_iff` — the double-collision bound is an equality **iff**
  no point is covered three times: the machinery is sharp exactly on families of
  *bounded multiplicity 2*.
* `cauchySchwarz_tight_iff_regular` — the Cauchy–Schwarz (Corrádi) bound is an
  equality **iff** the cover is *regular*, i.e. the multiplicity is constant.

Machine-learning reading: the Bonferroni union bound is lossless exactly for
ensembles whose failure sets never overlap, and the second-order Corrádi bound
is lossless exactly for ensembles whose failures are spread perfectly evenly
over the sample space — a formal statement of "the union bound is tight iff the
errors are uncorrelated, the second-moment bound is tight iff they are equally
correlated".
-/

namespace BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Regular covers -/

/-- The family covers each point of its union exactly `d` times. -/
def IsRegularCover (I : Finset ι) (A : ι → Finset Ω) (d : ℕ) : Prop :=
  ∀ x ∈ cover I A, mult I A x = d


/-! ## The exact Bonferroni defect -/





/-! ## Tightness of the double-collision bound -/


/-! ## Tightness of the Cauchy–Schwarz (Corrádi) bound -/



end BonferroniMarginals


