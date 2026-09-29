-- Prove2me | Theorems.Thm_mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
-- name    : mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:15:37.392155+00:00
-- url     : https://prove2.me/theorems/8eb6a28c-e75d-4864-9707-fe1afc9a2295
-- title:
--   Transport a useful-block nonhole to the completed fine-Z address
-- statement:
--   Fix a finite retained family and a useful fine-$Z$ block $z_j$ selected for one distinguished copy $j$. Suppose $z_j$ is a literal nonhole for the compatibility relation used by the Claim-6.8 collision fiber. Assume that, on this selected block, source compatibility with any copy is equivalent to compatibility of the encoded fine-nine address. Then the canonical completed mode-$2$ address is a literal nonhole for the address-level broken copy:
--
--   $$
--   z_j\in\operatorname{nonholes}(C_j^{\mathrm{source}})
--   \quad\Longrightarrow\quad
--   A_j^{(2)}\in\operatorname{nonholes}(C_j^{\mathrm{address}}).
--   $$
--
--   The conclusion transfers both ownership facts contained in nonhole membership: compatibility with $j$ and incompatibility with every competing retained copy. This is the finite semantic adapter between Claim 6.8 and the Step-2 direct-sum restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3, Claim 6.8, and Additional Zeroing-Out Step 2, printed pp. 51-57 (PDF pp. 52-58); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_completed_fine_z_address_eq_useful_block_encode
import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_step2_broken_copy

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false

theorem mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
    (m : ℕ) {Copy : Type v} {Position : Type u}
    [Fintype Copy] [DecidableEq Copy]
    [Fintype Position] [DecidableEq Position]
    (outer : Copy → Position → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (j : Copy)
    (sourceCompatible :
      MME.DWZTable2StandardForm.UsefulBlock m (outer j) → Copy → Prop)
    [DecidableRel sourceCompatible]
    (hSourceNonhole :
      small j ∈ (MME.DWZStep2.brokenCopy sourceCompatible
        (fun _ _ ↦ True) j).nonholes)
    (hCompatibleIff : ∀ j' : Copy,
      sourceCompatible (small j) j' ↔
        retainedFineCompatible m outer
          (fun t ↦
            fineSplitGrade ((small j).1 t).1 ((small j).1 t).2) j') :
    let left : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineLeft (outer j') (small j').1 (small j').2.1
    let right : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineRight (outer j') (small j').1 (small j').2.1
    retainedFineAddress left right j 2 ∈
      (MME.DWZStep2.brokenCopy
        (retainedFineCompatible m outer) (fun _ _ ↦ True) j).nonholes := by
  sorry
