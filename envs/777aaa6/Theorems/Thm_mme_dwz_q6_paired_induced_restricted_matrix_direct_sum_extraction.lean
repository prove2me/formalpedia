-- Prove2me | Theorems.Thm_mme_dwz_q6_paired_induced_restricted_matrix_direct_sum_extraction
-- name    : mme_dwz_q6_paired_induced_restricted_matrix_direct_sum_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:35:41.623346+00:00
-- url     : https://prove2.me/theorems/43ebe989-2c6b-4a0a-a5bc-ffd987ed54d8
-- title:
--   Paired-induced families extract matrix direct sums from the restricted 121 and 211 sources
-- statement:
--   Let $K$ be a field, let $s\in\{13,14\}$ index the canonical 121 or 211 component, and put $N=c_s m$. Suppose a primary $q=6$ family with $A$ outer fibers and $H$ entries per fiber has a common balanced halving and is paired-cyclic-induced. Write $R_{s,m}$ for its literal allowed-word component power. Then there are nonnegative matrix dimensions $a_j,b_j,c_j$, indexed by the $AH$ entries, such that
--   $$\bigoplus_{j=1}^{AH}\langle a_j,b_j,c_j\rangle\ \leq\ R_{s,m}\otimes\operatorname{swap}_{12}(R_{s,m}),\qquad a_jb_jc_j=6^{4G+2L}.$$
--   Here $\leq$ denotes tensor restriction by mode-wise linear maps. The source uses the prescribed split-count projection on the third mode, not the unprojected component power. The conclusion retains every entry of the paired-induced family and permits heterogeneous matrix dimensions. Paired inducedness remains an explicit hypothesis; no bound on the size of such a subfamily is asserted.
-- source:
--   Combines the paired-induced component projection construction with the canonical 121 and 211 ambient source maps, disallowed-word descent through the literal component-pair inclusion, and the accepted matrix component certificate.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
universe u
set_option autoImplicit false

theorem mme_dwz_q6_paired_induced_restricted_matrix_direct_sum_extraction
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) :
    ∃ a b c : Fin (A * H) → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (componentPairRestricted K s m) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by sorry
