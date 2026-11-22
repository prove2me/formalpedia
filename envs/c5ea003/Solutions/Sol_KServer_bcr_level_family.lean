-- Prove2me | solution 1 for KServer.bcr_level_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T16:43:16.950956+00:00
-- url     : https://prove2.me/submissions/f38a1e9e-d9e1-4ffa-b5c8-b594c24b311c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bcr_space2
import Theorems.Thm_KServer_bcr_level_system

open KServer

theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℕ, 0 < β ∧ ∀ w : ℕ,
      ∃ (X : Type) (mX : MetricSpace X) (fX : Fintype X) (s t : X),
        @Fintype.card X fX ≤ (β + 1) * 6 ^ w ∧
        @dist X mX.toDist s t = (β : ℝ) * 3 ^ w ∧
        ∃ (cHi price : ℝ) (M : ℕ)
          (C : @ChunkSystemB X mX s t 0 cHi
            (α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w)) price M),
          0 ≤ price ∧ (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) := by
  obtain ⟨α, hα, β, hβ, H⟩ := KServer.bcr_level_system
  refine ⟨α, hα, β, hβ, fun w => ?_⟩
  obtain ⟨cHi, price, M, C, hprice, htriv⟩ := H w
  refine ⟨(bcrLevel2 β hβ w).carrier, (bcrLevel2 β hβ w).metric,
    (bcrLevel2 β hβ w).fin, (bcrLevel2 β hβ w).s, (bcrLevel2 β hβ w).t,
    bcrLevel2_card_le β hβ w, bcrLevel2_dist_st β hβ w,
    cHi, price, M, C, hprice, htriv⟩
