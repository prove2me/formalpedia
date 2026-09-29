-- Prove2me | Theorems.Thm_BonferroniMarginals_sharp_bonferroni_defect_identity
-- name    : BonferroniMarginals.sharp_bonferroni_defect_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:27:09.117218+00:00
-- url     : https://prove2.me/theorems/2e046e50-ed7a-4fed-a66d-cc6f74e68995
-- title:
--   Exact defect of the sharp second Bonferroni inequality.
-- statement:
--   **Exact defect of the sharp second Bonferroni inequality.**
--
--   ```lean
--   theorem BonferroniMarginals.sharp_bonferroni_defect_identity(I : Finset ι) (A : ι → Finset Ω) :
--       2 * ∑ i ∈ I, (A i).card
--           + ∑ x ∈ cover I A, (mult I A x - 1) * (mult I A x - 2)
--         = 2 * (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/SharpBonferroni.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/SharpBonferroni.lean#L41

-- Thm stub generated from MachineLearning/BonferroniMarginals/SharpBonferroni.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability

/-!
# The sharp (unordered-pair) second Bonferroni inequality

`Core.lean` proves
`∑ᵢ|Aᵢ| ≤ |cover| + ∑_{(i,j) ∈ offDiag}|Aᵢ ∩ Aⱼ|`,
where the pair sum runs over *ordered* pairs and therefore counts every overlap
twice.  The classical second Bonferroni inequality is the unordered statement
`∑ᵢ|Aᵢ| − ∑_{i<j}|Aᵢ ∩ Aⱼ| ≤ |cover|`,
which is a factor `2` stronger on the correction term.  This file proves it in
the index-order-free form

`2·∑ᵢ|Aᵢ| ≤ 2·|cover| + ∑_{(i,j) ∈ offDiag}|Aᵢ ∩ Aⱼ|`

together with its exact defect and its tightness characterisation.

* `sharp_bonferroni_defect_identity` —
  `2·∑ᵢ|Aᵢ| + ∑ₓ (mult x − 1)(mult x − 2) = 2·|cover| + ∑_{i≠j}|Aᵢ ∩ Aⱼ|`.
  The defect is now the *second factorial* deviation of the multiplicity from
  the interval `{1, 2}`, rather than the squared deviation from `1`.
* `sharp_bonferroni` — the inequality.
* `sharp_bonferroni_tight_iff` — equality holds iff no point is covered three
  times, i.e. exactly on the families for which the double-collision bound
  `card_doubleCollision_mul_le` is also tight (`doubleCollision_tight_iff`).
  The two second-order inequalities of the machinery therefore have *the same*
  extremal class: multiplicity-`≤ 2` families.
* `sharp_bonferroni_strictly_stronger` — the sharp bound implies the
  `Core.lean` bound.

Machine-learning reading: the classical union-bound correction is exactly
lossless for ensembles in which no sample is misclassified by three or more
members; beyond that regime the correction over-counts, by a computable amount.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω] [DecidableEq ι]

theorem BonferroniMarginals.sharp_bonferroni_defect_identity(I : Finset ι) (A : ι → Finset Ω) :
    2 * ∑ i ∈ I, (A i).card
        + ∑ x ∈ cover I A, (mult I A x - 1) * (mult I A x - 2)
      = 2 * (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by sorry
