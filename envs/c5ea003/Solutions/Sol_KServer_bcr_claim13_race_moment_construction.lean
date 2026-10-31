-- Prove2me | solution 1 for KServer.bcr_claim13_race_moment_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T16:53:52.92461+00:00
-- url     : https://prove2.me/submissions/a65d6cf4-50cc-44ac-a186-145534e62848
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_race_kernel_construction
import Theorems.Thm_KServer_race_kernel_moments
open KServer

theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ Z : C.Ω → ℝ,
          (Real.sqrt (α * β) * (w : ℝ)) ^ 2 / 4 ≤ (∑ ω, C.P ω * Z ω ^ 2) ∧
          (∑ ω, C.P ω * Z ω ^ 4) ≤ 4 * (Real.sqrt (α * β) * (w : ℝ)) ^ 4 ∧
          (3 * (α * β) * (w : ℝ) ^ 2 + (∑ ω, C.P ω * |Z ω|) / 2) * 3 ^ w
            ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
          pe ≤ (β : ℝ) * 3 ^ w ∧
          cB + jb ≤ 11 / 8 * (3 : ℝ) ^ w ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
          (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
          C.DoobJumpBound jb  := by
  classical
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R,
    hzero, hlr, hstep, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_race_kernel_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  have hden : ∀ j < N, ∀ ω, L j ω + R j ω ≠ 0 := by
    intro j hj ω
    exact ne_of_gt (hlr j hj ω).2.2
  obtain ⟨hsq, hfour⟩ := race_kernel_moments C.P S L R N hzero hden hstep
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, S N, ?_, ?_, hmass, hp, hb, h0, hch, hjump⟩
  · rw [hsq]
    exact hvar
  · rw [hfour]
    exact hquartic