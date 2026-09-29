-- Prove2me | Definitions.Def_mme_dwz_profiled_regional_keep_data
-- name    : mme_dwz_profiled_regional_keep_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T18:55:39.847899+00:00
-- url     : https://prove2.me/theorems/24b2e859-2626-4ad3-a114-629180f02165
-- title:
--   The regional keep predicate of the asymmetric fourth-power source
-- statement:
--   The inherited-profile predicate cut out by the Duan-Wu-Zhou regional zero-out at the fourth level: a physical word is kept when, in every region and at every fourth-power position, the grades of its two half-words sum to the parent block type of that mode, and when, in the mode kept by the region, the left-half grades realize the region's integer Z-profile exactly.
-- source:
--   Definition 3.9 and the regional zero-out of the Duan-Wu-Zhou fourth-power construction, in the form used by the asymmetric hashing stage. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_dwz_prescribed_z_split_value

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.DWZRestrictedValue
open scoped Classical

universe u

set_option autoImplicit false

namespace MME.DWZProfiledRegional

/-- The inherited-profile predicate cut out by the Duan-Wu-Zhou regional zero-out at the
fourth level.  A physical word is kept when, in every region `r` and at every position `t`,
its two half-words carry the parent block type of the mode, and when, in the mode kept by
that region, the left grades realize the region's integer `Z`-profile exactly. -/
def dwzKeep {R L N : ℕ} (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (keptMode : Fin R → Fin 3) (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (2 - 1) = N) :
    ProfiledCW.Predicate N := fun i x ↦
  let f : Position n → CompleteWord 2 :=
    ProfiledCW.split (ell := 2) positions length x
  (∀ r t, CWCells.grade (f ⟨r, t, 0⟩) + CWCells.grade (f ⟨r, t, 1⟩) = parent r i) ∧
  (∀ r, i = keptMode r → ∀ j : Fin 5,
    (Finset.univ.filter
      (fun t : Fin (n r) ↦ CWCells.grade (f ⟨r, t, 0⟩) = j.val)).card
      = (p r).count j * scale r)

end MME.DWZProfiledRegional


