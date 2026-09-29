-- Prove2me | Theorems.Thm_mme_dwz_q6_121_normalized_primary_hash_star_restrict
-- name    : mme_dwz_q6_121_normalized_primary_hash_star_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:16:30.08649+00:00
-- url     : https://prove2.me/theorems/5658b0cb-fd8f-4816-8cac-df4954918633
-- title:
--   Primary shared-Z stars restrict from normalized row 121
-- statement:
--   Set $N=1036722900000000m$. For every exact primary hash family in the $2N$-fold coupled tensor, the direct sum of its $A$ shared-$Z$ outer stars is a restriction of the literal row-121 restricted component after one cyclic normalization:
--
--   $$
--   \bigoplus_{a=1}^{A} \operatorname{Star}_a \preceq c\bigl(T_{121}^{\otimes 2N}[\mathrm{available}]\bigr).
--   $$
--
--   The cyclic normalization exactly cancels the twice-cyclic orientation produced by the row-121 source router. This theorem is the source-sensitive tensor landing required to package the retained stars as a family of C-tensors without restoring any discarded basis words.
-- source:
--   Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3 and Table 2, row 121; source-sensitive realization using Definition 5.4 availability and the Coppersmith--Winograd shared-variable extraction.

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_permutation

open MME MME.TensorObj MME.DWZComponentRestriction
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_normalized_primary_hash_star_restrict
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (starObj (dwzQ6CoupledGrading K) family))
      (TensorObj.permObj cyclicPerm
        (restrictedComponentPower K (13 : Fin 15) m)) := by
  sorry
