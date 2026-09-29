-- Prove2me | Definitions.Def_mme_dwz_table2_standard_obj
-- name    : mme_dwz_table2_standard_obj
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:22:04.783327+00:00
-- url     : https://prove2.me/theorems/f90e0838-2ffa-481f-80fb-d876f090ff83
-- title:
--   Literal complete Table-2 standard-form tensor
-- statement:
--   For a field $K$ and integral scale $m\geq 0$, define the complete Table-2 standard-form tensor $T^*(m)$ as the ordered Kronecker product over the fifteen literal $q=6$ CW-square component types. The factor at row $s$ is the already-defined source-faithful $Z$-only available-word restriction of the canonical component power with exponent $n_s m$. Thus
--
--   $$
--   T^*(m)=\bigotimes_{s=0}^{14} T_s^{\otimes n_s m}[\widetilde\alpha_s].
--   $$
--
--   This definition retains all $X$ and $Y$ variables in each component factor and restricts only its $Z$ word basis. It is the complete standard object prior to any useful-small-block decomposition or hole removal, and it includes $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 (standard form), Definitions 5.3--5.4 (restricted-splitting component factors), and Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_CW_2376_address_block

open MME

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- The complete DWZ Table-2 standard-form tensor at scale `m`: the ordered
Kronecker product of the fifteen literal Z-restricted component powers. -/
noncomputable def dwzTable2StandardObj (K : Type u) [Field K] (m : ℕ) :
    TensorObj K 3 :=
  TensorObj.kronFin 15 (fun s ↦ restrictedComponentPower K s m)

end MME.DWZComponentRestriction


