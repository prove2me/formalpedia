-- Prove2me | Theorems.Thm_QRResidual_exists_perm_two_point
-- name    : QRResidual.exists_perm_two_point
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:50:23.175212+00:00
-- url     : https://prove2.me/theorems/0a7aa8b2-97d9-44ee-9c8f-65b02cd7bfc4
-- title:
--   Sharp 2-transitivity of `S_n`, in explicit two-swap form: any ordered pair of
-- statement:
--   **Sharp 2-transitivity of `S_n`**, in explicit two-swap form: any ordered pair of
--   distinct points can be moved to any other ordered pair of distinct points.
--
--   ```lean
--   theorem QRResidual.exists_perm_two_point{i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j') :
--       ∃ τ : Equiv.Perm ι, τ i' = i ∧ τ j' = j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/QRResidual/PermutationNull.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/QRResidual/PermutationNull.lean#L50

-- Thm stub generated from MachineLearning/QRResidual/PermutationNull.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_PermutationNull

/-!
# Exact calibration of the permutation null for an `R²` increment

The verdict of experiment 585 rests on two numbers: an observed increment
`ΔR² = 0.01946`, and a permutation null obtained from 500 joint row-shuffles of the
covariate block, with `p = 0.389` and `q95 = 0.046`.  The permutation null is normally
treated as a Monte-Carlo object.  It is not: for a *single* centred covariate its exact
first moment is a closed-form function of the sample size alone.

Main results.

* `exists_perm_two_point` — sharp 2-transitivity of the symmetric group, in the explicit
  two-swap form needed below.
* `permSum_pair_const_offdiag`, `permSum_pair_const_diag` — the sum
  `W(i,j) = Σ_{σ} v(σ i) v(σ j)` over the whole symmetric group depends only on whether
  `i = j`.
* `perm_null_sum_sq_dot` — **the calibration identity**: for a centred residual `r` and a
  centred covariate `v` on a sample of size `n`,
  `Σ_{σ ∈ S_n} ⟨r, v∘σ⟩² = n! · ‖r‖²‖v‖² / (n−1)`,
  i.e. the *mean squared* residual correlation under a random row shuffle is exactly
  `1/(n−1)` of the maximum.
* `perm_null_mean_lift` — hence the mean permutation-null `R²` increment of one covariate
  is exactly `(1 − R²₀)/(n − 1)`: the null is calibrated by the baseline fit and the sample
  size, with no distributional assumption whatsoever.
* `perm_null_tail`, `exp585_perm_null_tail` — a Markov tail bound on the null, and its
  numeric instance: at the reported baseline `R²₀ = 0.4112` and any sample of at least
  `237` moduli, at most a `0.05` fraction of shuffles reach an increment of `0.05`.  This
  is consistent with, and independently bounds, the reported `q95 = 0.046`.

Together with `BlockCeiling`, this turns the experiment's null verdict into two theorems:
a *ceiling* on what the covariate block could ever have achieved, and a *calibration* of
the reference distribution against which the observed increment was judged.
-/

open QRResidual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Reindexing sums over the symmetric group -/


omit [Fintype ι] in

theorem QRResidual.exists_perm_two_point{i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ τ : Equiv.Perm ι, τ i' = i ∧ τ j' = j := by sorry
