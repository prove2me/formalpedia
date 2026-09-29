-- Prove2me | Theorems.Thm_QuantumEML_root_mem_Icc_six_fifths_five_fourths
-- name    : QuantumEML.root_mem_Icc_six_fifths_five_fourths
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:39:24.834902+00:00
-- url     : https://prove2.me/theorems/6102b58d-839d-4a89-b141-d1f9d90f6daa
-- title:
--   Every positive solution lies in the tightened interval `[6/5, 5/4]`.
-- statement:
--   Every positive solution lies in the tightened interval `[6/5, 5/4]`.
--
--   ```lean
--   theorem QuantumEML.root_mem_Icc_six_fifths_five_fourths{t : ℝ} (ht : 0 < t) (h : scalarLogNorm t = 1) :
--       t ∈ Icc (6 / 5 : ℝ) (5 / 4) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/EMLQuantumScalarLogSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/EMLQuantumScalarLogSharp.lean#L250

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

theorem QuantumEML.root_mem_Icc_six_fifths_five_fourths{t : ℝ} (ht : 0 < t) (h : scalarLogNorm t = 1) :
    t ∈ Icc (6 / 5 : ℝ) (5 / 4) := by sorry
