-- Prove2me | Theorems.Thm_mme_dwz_q6_selected_paired_induced_restricted_matrix_extraction
-- name    : mme_dwz_q6_selected_paired_induced_restricted_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:58:27.069242+00:00
-- url     : https://prove2.me/theorems/7e924354-face-49a9-9fe6-cd8f78831788
-- title:
--   Any paired-induced entry selection extracts matrix blocks from the restricted pair
-- statement:
--   Let $K$ be a field, $s\in\{13,14\}$ a canonical component, and $N=c_s m$. Let a primary $q=6$ family with $A$ fibers and $H$ entries per fiber have a common balanced halving. Choose $q$ indexed entries such that every paired-cyclic supported triple among them has three equal indices. Writing $R_{s,m}$ for the allowed-word restricted component power and $\sigma$ for the swap of the first two tensor modes, there exist matrix dimensions satisfying
--   $$\bigoplus_{j=1}^{q}\langle a_j,b_j,c_j\rangle\leq R_{s,m}\otimes\sigma R_{s,m},\qquad a_jb_jc_j=6^{4G+2L}.$$
--   Thus any paired-induced selection gives matrix blocks from the literal restricted pair. The statement assumes neither a coloring of the whole conflict graph nor uniform numbers of selected entries per fiber. It does not assert that a large selection exists.
-- source:
--   Selected component projections, disallowed-word descent, component matrix certificates, and cyclic expansion of equal-volume matrix sums.

import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MME MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

theorem mme_dwz_q6_selected_paired_induced_restricted_matrix_extraction
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (q : ℕ) (index : Fin q → Fin A × Fin H)
    (hselected : ∀ p0 p1 p2, family.PairedCyclicSupported halving
      (index p0) (index p1) (index p2) → p0 = p1 ∧ p1 = p2) :
    ∃ a b c : Fin q → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (componentPairRestricted K s m) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by sorry
