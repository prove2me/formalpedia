-- Prove2me | Theorems.Thm_QuantumEML_continuous_scalarLogNorm
-- name    : QuantumEML.continuous_scalarLogNorm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:39:02.603465+00:00
-- url     : https://prove2.me/theorems/f0a0ec0d-acd0-4f4b-a576-66b6487f394a
-- title:
--   The line `1 + t i` stays in the slit plane, hence its principal logarithm
-- statement:
--   The line `1 + t i` stays in the slit plane, hence its principal logarithm
--   and its norm vary continuously.
--
--   ```lean
--   theorem QuantumEML.continuous_scalarLogNorm: Continuous scalarLogNorm := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/EMLQuantumScalarLogRootIsolation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/EMLQuantumScalarLogRootIsolation.lean#L324

-- Thm stub generated from NumberTheory/EMLQuantumScalarLogSharp.lean
import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLogSharp

/-!
# Sharpening the scalar unitary logarithmic factor

This file continues the study of the *scalar-log unit-circle* problem for
quantum EML activations begun in `Catalog/NumberTheory/EMLQuantumScalarLog.lean`,
where the existence of a parameter `t ≠ 0` with `‖log (1 + t i)‖ = 1` was
established with the crude certified interval `[1/2, 3]`.  (The catalog files
are compiled independently of one another, so the two basic definitions
`scalarLogNorm` and the auxiliary lemmas are restated here verbatim; everything
past that point is new.)

The results proved here answer the first three of the "future directions"
attached to that file, and add a fourth.

## Main results

* `QuantumEML.scalarLogNorm_sq` : the closed form
  `‖log (1 + t i)‖ ^ 2 = (log (1 + t ^ 2) / 2) ^ 2 + arctan t ^ 2`.
* `QuantumEML.strictMonoOn_scalarLogNorm` : `t ↦ ‖log (1 + t i)‖` is *strictly
  increasing* on `[0, ∞)`.  This upgrades the previous existence statement to a
  uniqueness statement.
* `QuantumEML.existsUnique_pos_scalarLogNorm_eq_one` : there is exactly one
  positive solution of `‖log (1 + t i)‖ = 1`.
* `QuantumEML.scalarLogNorm_six_fifths_lt_one`,
  `QuantumEML.one_lt_scalarLogNorm_five_fourths`,
  `QuantumEML.root_mem_Icc_six_fifths_five_fourths` : the certified interval is
  tightened from `[1/2, 3]` to `[6/5, 5/4]`, a factor `30` improvement in
  width.  The proof uses the exact `arctan` addition identities
  `arctan (6/5) = π/4 + arctan (1/11)` and `arctan (5/4) = π/4 + arctan (1/9)`
  together with the elementary two-sided bound
  `y / (1 + y ^ 2) ≤ arctan y ≤ y` and the rational bounds
  `1 - x⁻¹ ≤ log x ≤ x - 1` applied after splitting off `log 2`.
* `smul_one_mem_unitary` : a scalar of modulus one times the identity of any
  complex star algebra is unitary; hence the scalar logarithmic factor lifts to
  matrix C⋆-algebras (`QuantumEML.exists_scalar_log_smul_one_mem_unitary`).
* `QuantumEML.polarUnit_smul_one_mem_unitary` : the *polar-normalized*
  logarithmic factor `log (1 + t i) / ‖log (1 + t i)‖` is unitary for **every**
  `t ≠ 0`, not merely for the certified root.
-/

noncomputable section

open Complex Real Set

/-! ### A scalar of modulus one is a unitary in any complex star algebra -/




/-! ### Elementary two-sided bounds for `arctan` -/

open QuantumEML





/-! ### The scalar logarithmic norm and its closed form -/









/-! ### Strict monotonicity and uniqueness -/





/-! ### The tightened certified interval `[6/5, 5/4]` -/

theorem QuantumEML.continuous_scalarLogNorm: Continuous scalarLogNorm := by sorry
