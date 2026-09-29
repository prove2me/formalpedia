-- Prove2me | Theorems.Thm_mme_dwz_q6_paired_coloring_restricted_matrix_direct_sum_extraction
-- name    : mme_dwz_q6_paired_coloring_restricted_matrix_direct_sum_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:39:04.175843+00:00
-- url     : https://prove2.me/theorems/b35445eb-7852-434d-8090-0fdc380ce6f6
-- title:
--   A paired conflict coloring extracts a matrix direct sum from the restricted component pair
-- statement:
--   Let $K$ be a field, let $s\in\{13,14\}$ index the canonical 121 or 211 component, and let a primary $q=6$ family of length $N=c_s m$ have $A$ outer fibers, $H$ entries per fiber, and a common balanced halving. Suppose its paired-cyclic conflict graph has a proper coloring with $k>0$ colors. If $R_{s,m}$ denotes the literal allowed-word component power, then there are $Q$ matrix tensors satisfying
--   $$AH\leq kQ,\qquad \bigoplus_{j=1}^{Q}\langle a_j,b_j,c_j\rangle\ \leq\ R_{s,m}\otimes\operatorname{swap}_{12}(R_{s,m}),\qquad a_jb_jc_j=6^{4G+2L}.$$
--   The restriction uses the prescribed third-mode split-count projection. The retained entries need not form uniform outer fibers, and their matrix dimensions may differ. This is a bound on the number of extracted blocks; it does not assert preservation of the stronger outer-fiber capacity factor $A^3H^2$.
-- source:
--   Pigeonhole selection of a largest color class, paired-inducedness of a monochromatic conflict-free selection, explicit component direct-sum projections, canonical 121/211 source routing, and disallowed-word descent to the literal restricted pair.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
universe u
set_option autoImplicit false

theorem mme_dwz_q6_paired_coloring_restricted_matrix_direct_sum_extraction
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ) {k : ℕ}
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      A * H ≤ k * q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (componentPairRestricted K s m) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by sorry
