-- Prove2me | Definitions.Def_mme_released_global_yz_word_data
-- name    : mme_released_global_yz_word_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T12:50:05.99617+00:00
-- url     : https://prove2.me/theorems/0e301654-b07b-4b80-8719-6f790872f570
-- title:
--   Exact global Y/Z certificate: word data
-- statement:
--   One component of the exact six-orientation Y/Z certificate: word enumeration and cached integer counts, finite entropy expressions, or outward-rounded logarithm intervals. All numerical data are connected to the published profile by the accompanying full proofs. Tables are split by orientation to fit publication and compilation limits.
-- source:
--   Exact released global candidate from primitive seed f8187420c24231b83d9d1fb7b327fee76cd50ada0af0525e77b3d3b0d8f4d4e6.

import Definitions.Def_mme_released_global_yz_words_0
import Definitions.Def_mme_released_global_yz_words_1
import Definitions.Def_mme_released_global_yz_words_2
import Definitions.Def_mme_released_global_yz_words_3
import Definitions.Def_mme_released_global_yz_words_4
import Definitions.Def_mme_released_global_yz_words_5
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace MME.ReleasedGlobalYZ

def codeWord (t : Fin 81) : Word := fun r ↦ ⟨t.val / 3^r.val % 3, Nat.mod_lt _ (by decide)⟩
def wordIndex (v : Word) : ℕ := ∑ r : Fin 4, (v r).val * 3^r.val
noncomputable def wordEquiv : Fin 81 ≃ Word := Equiv.ofBijective codeWord (by
  have hl : ∀ t : Fin 81, wordIndex (codeWord t) = t.val := by decide +kernel
  have hi : Function.Injective codeWord := by
    intro a b h
    apply Fin.ext
    simpa only [hl] using congrArg wordIndex h
  apply (Fintype.bijective_iff_injective_and_card codeWord).mpr
  exact ⟨hi,by decide +kernel⟩)

def cachedCounts : Fin 6 → Fin 2 → Fin 45 → Fin 81 → ℕ := ![wordCountsOwner0,wordCountsOwner1,wordCountsOwner2,wordCountsOwner3,wordCountsOwner4,wordCountsOwner5]

end MME.ReleasedGlobalYZ


