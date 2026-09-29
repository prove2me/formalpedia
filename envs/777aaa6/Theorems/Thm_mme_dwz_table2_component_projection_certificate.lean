-- Prove2me | Theorems.Thm_mme_dwz_table2_component_projection_certificate
-- name    : mme_dwz_table2_component_projection_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:08:28.512855+00:00
-- url     : https://prove2.me/theorems/c7c80ead-c743-44db-9dc0-01574d5907da
-- title:
--   Each restricted Table-2 component power is a genuine Z-only projection
-- statement:
--   For every Table-2 component $s$ at $q=6$ and every scale $m\geq0$, let $B_s$ be the literal canonical five-graded component block and let $n_s$ be its exact integer multiplicity. Let $B_s^{\otimes n_sm}[\widetilde\alpha_s]$ be the tensor obtained by retaining exactly the available canonical $Z$ words. Then
--
--   $$
--   B_s^{\otimes n_sm}[\widetilde\alpha_s]\leq B_s^{\otimes n_sm}.
--   $$
--
--   Moreover, the selected $X$ and $Y$ grading classes are their complete mode spaces, while the selected $Z$ class is exactly the span of the available canonical word basis. Hence this restriction is one genuine $Z$-mode projection: it does not clone or independently split the shared $X$ and $Y$ variables.
--
--   Together with the separate exact-histogram theorem, this is the source-faithful component factor used in the standard-form tensor $T^*$ of Definition 5.2. The statement includes $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Definitions 5.2--5.4, PDF pp. 47--48 / printed pp. 46--47, specialized to q=6 and Table 2 in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_table2_component_projection_certificate
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    TensorObj.Restrict
        (MME.DWZComponentRestriction.restrictedComponentPower K s m)
        ((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
          (MME.DWZTable2Counts.component s * m)) ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          0 0 = ⊤ ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          1 0 = ⊤ ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          2 0 =
        Submodule.span K
          (MME.DWZComponentRestriction.componentPowerZBasis K s m ''
            {w | MME.DWZComponentRestriction.componentWordAllowed s m w}) := by
  sorry
