-- Prove2me | Theorems.Thm_BonferroniMarginals_mult_eq_one_iff_pairwiseDisjoint
-- name    : BonferroniMarginals.mult_eq_one_iff_pairwiseDisjoint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:26:55.971579+00:00
-- url     : https://prove2.me/theorems/53a2c911-f463-443e-b549-a677ef6a16f7
-- title:
--   Multiplicity one everywhere is the same as pairwise disjointness of the family.
-- statement:
--   Multiplicity one everywhere is the same as pairwise disjointness of the family.
--
--   ```lean
--   theorem BonferroniMarginals.mult_eq_one_iff_pairwiseDisjoint(I : Finset ι) (A : ι → Finset Ω) :
--       (∀ x ∈ cover I A, mult I A x = 1)
--         ↔ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/Rigidity.lean#L93

-- Thm stub generated from MachineLearning/BonferroniMarginals/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity

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

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Regular covers -/



/-! ## The exact Bonferroni defect -/

theorem BonferroniMarginals.mult_eq_one_iff_pairwiseDisjoint(I : Finset ι) (A : ι → Finset Ω) :
    (∀ x ∈ cover I A, mult I A x = 1)
      ↔ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j) := by sorry
