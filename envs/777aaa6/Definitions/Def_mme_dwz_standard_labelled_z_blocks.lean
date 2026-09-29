-- Prove2me | Definitions.Def_mme_dwz_standard_labelled_z_blocks
-- name    : mme_dwz_standard_labelled_z_blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T10:24:18.859142+00:00
-- url     : https://prove2.me/theorems/5178ae66-ce8f-4798-8a4f-4bbaac50454b
-- title:
--   Grouped useful-block Z restrictions of the Table-2 standard tensor
-- statement:
--   The canonical Table-2 standard tensor is bundled with its grouped Z basis and with the useful-block label of every grouped basis word. For a useful block b, the associated tensor contribution is the literal restriction obtained by fixing X and Y and projecting Z onto exactly the basis words labelled by b. Thus the definition records an actual tensor-mode restriction, not merely the number of words in a block. This bundled interface also preserves the dependent fact that the grouped basis is a basis of the standard object actual Z mode.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 5.4 (available blocks), Section 5 Hole Lemma repair, and Definition 6.3 (useful blocks), PDF pp.47 and 53 / printed pp.46 and 52.

import Definitions.Def_mme_dwz_basis_label_projection

open MME Module PiTensorProduct

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- Useful-block labels for the canonically grouped Table-2 standard object. -/
abbrev DWZStandardBlock (m : ℕ) :=
  MME.DWZTable2StandardForm.UsefulBlock m (groupedOuter (m := m))

/-- The standard object bundled with its grouped Z basis and useful-block
label. -/
structure DWZStandardLabelledData (K : Type u) [Field K] (m : ℕ) where
  X : TensorObj K 3
  basis : Basis (GroupedAllowedWords.{u} m) K (X.V 2)
  label : GroupedAllowedWords.{u} m → DWZStandardBlock m

/-- The canonical grouped-Z-labelled Table-2 standard object. -/
noncomputable def dwzStandardLabelledData
    (K : Type u) [Field K] (m : ℕ) : DWZStandardLabelledData K m where
  X := dwzTable2StandardObj K m
  basis := dwzTable2StandardZBasis K m
  label := groupedUsefulBlock m

/-- The exact tensor contribution with one useful-block label in bundled
standard data. -/
noncomputable def dwzLabelledUsefulBlockTensor
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) (block : DWZStandardBlock m) :
    PiTensorProduct K D.X.V :=
  PiTensorProduct.map
    (Function.update (fun _ ↦ LinearMap.id) 2
      (basisLabelProjection D.basis D.label {block}))
    D.X.t

/-- The exact tensor contribution of one useful-block label in the canonical
Table-2 standard object. -/
noncomputable def dwzStandardUsefulBlockTensor
    (K : Type u) [Field K] (m : ℕ) (block : DWZStandardBlock m) :
    PiTensorProduct K (dwzStandardLabelledData K m).X.V :=
  dwzLabelledUsefulBlockTensor K m (dwzStandardLabelledData K m) block

end MME.DWZComponentRestriction


