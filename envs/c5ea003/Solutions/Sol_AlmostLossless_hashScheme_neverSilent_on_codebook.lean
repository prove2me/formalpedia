-- Prove2me | solution 1 for AlmostLossless.hashScheme_neverSilent_on_codebook
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:13:30.720291+00:00
-- url     : https://prove2.me/submissions/c8524b53-9492-408d-bd1d-b44578d98215

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Theorems.Thm_AlmostLossless_decodeList_never_wrong_on_codebook
set_option autoImplicit false
open AlmostLossless

theorem solution {α : Type*} {M : ℕ} {l : List α} {h : α → Fin M} {x : α}
    (hx : x ∈ l) : ¬ (hashScheme l h).SilentError x := by
  letI : Nonempty α := ⟨x⟩
  rintro ⟨y, hy, hne⟩
  exact hne (decodeList_never_wrong_on_codebook hx hy)
#print axioms solution
