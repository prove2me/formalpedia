-- Prove2me | solution 2 for KServer.bcr_level_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T21:29:10.687733+00:00
-- url     : https://prove2.me/submissions/bda8687c-37a6-45af-8e67-56da2c513509
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bcr_space2
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_bcr_induction_tight
import Theorems.Thm_KServer_bcr_tight_base
import Theorems.Thm_KServer_bcr_tight_step

open KServer

theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℕ, ∃ hβ : 0 < β, ∀ w : ℕ,
      ∃ (cHi price : ℝ) (M : ℕ)
        (C : @ChunkSystemB (bcrLevel2 β hβ w).carrier (bcrLevel2 β hβ w).metric
          (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t 0 cHi
          (α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w)) price M),
        0 ≤ price ∧ (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) := by
  obtain ⟨α, hα, hα1, β, hβ, hβ2, step⟩ := bcr_tight_step
  have levels : ∀ w, BCRInductiveChunksTight α β hβ w := by
    intro w
    induction w with
    | zero =>
      refine bcr_tight_base α hα.le β hβ hβ2 0 ?_
      simp
    | succ w ih =>
      by_cases small : α * ((w + 1 : ℕ) : ℝ) ^ 2 ≤ 1
      · exact bcr_tight_base α hα.le β hβ hβ2 (w + 1) small
      · exact step w (lt_of_not_ge small) ih
  refine ⟨α, hα, β, hβ, fun w => ?_⟩
  obtain ⟨M, C, hm, hMge, h0, hne⟩ := levels w
  refine ⟨3 * (3 : ℝ) ^ w / 2, (β : ℝ) * 3 ^ w, M, ?_⟩
  refine ⟨C.adjust (cLo' := 0) (cHi' := 3 * (3 : ℝ) ^ w / 2)
      (T' := α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w)) (pe' := (β : ℝ) * 3 ^ w) (mLo' := M)
      (by positivity) le_rfl (by apply le_of_eq; ring) le_rfl le_rfl, ?_, ?_⟩
  · positivity
  · exact h0
