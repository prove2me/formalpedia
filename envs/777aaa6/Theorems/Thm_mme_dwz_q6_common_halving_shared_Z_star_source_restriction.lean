-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_shared_Z_star_source_restriction
-- name    : mme_dwz_q6_common_halving_shared_Z_star_source_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:52:52.432173+00:00
-- url     : https://prove2.me/theorems/0d1b584d-5a96-4e36-abf8-508e28b214fd
-- title:
--   DWZ common-halving source restricts to cyclic shared-Z stars
-- statement:
--   Let $K$ be a field and let $s\in\{13,14\}$ index a DWZ Table 2 component. For $m\in\mathbb N$, set $N=c_s m$, where $c_s$ is its component count. Let $\mathcal F$ be a primary coupled-address family with parameters $(N,L,G,A,H)$ and a common balanced X/Y halving. Write $S_a$ for its shared-Z star in the concrete coupled tensor at $q=6$, and $R_{s,m}$ for the restricted component power. Then $$\operatorname{cyc}\!\left(\bigoplus_{a=1}^{A}S_a\right)\preceq\operatorname{six}(R_{s,m}).$$ Here $\preceq$ denotes tensor restriction and cyc and six denote cyclic and full sixfold symmetrization. This supplies the original family of stars from the DWZ source. Certificates identifying the matrix blocks and quantitative volume bounds are separate conclusions.
-- source:
--   Primary-family masked outer extraction and common-halving aligned source restriction.

import Theorems.Thm_mme_primary_hash_family_masked_outer_extraction_map
import Theorems.Thm_mme_dwz_q6_common_halving_aligned_filtered_source_restriction
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction MME.CompleteSplit112
open Module PiTensorProduct CoupledCTensorPackaging
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_shared_Z_star_source_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.bigAdd (starObj (grading K 6) family)))
      (sixSymmetrization (restrictedComponentPower K s m)) := by sorry
