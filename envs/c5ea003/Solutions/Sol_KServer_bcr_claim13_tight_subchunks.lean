-- Prove2me | solution 1 for KServer.bcr_claim13_tight_subchunks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T02:13:42.972979+00:00
-- url     : https://prove2.me/submissions/ac7fb73c-43aa-48bb-be66-388cbeccf22d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_relative_efficiency
import Theorems.Thm_KServer_chunk_scale_sizes_price

open KServer

theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jbS : ℝ, 0 ≤ cB ∧ 0 ≤ jbS ∧ cB + jbS ≤ 11 / 8 * (3 : ℝ) ^ w ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) ((β : ℝ) * 3 ^ w) 0,
        (∑ ω, C.P ω * ∑ i, C.size ω i)
            = (α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1) ∧
        (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
        (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
        C.DoobJumpBound jbS := by
  classical
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, hmass, hprice, hbudget, h0, hch, hjump⟩ :=
    bcr_claim13_relative_efficiency α hα hα1 β hβ hβ2 hsmall w hw hC
  let T : ℝ := (α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)
  let S : ℝ := ∑ ω, C.P ω * ∑ i, C.size ω i
  have hT : 0 < T := by dsimp [T]; positivity
  have hS : 0 < S := lt_of_lt_of_le hT hmass
  let q : ℝ := T / S
  have hq0 : 0 ≤ q := div_nonneg hT.le hS.le
  have hq1 : q ≤ 1 := (div_le_one hS).mpr hmass
  have hqS : q * S = T := div_mul_cancel₀ T hS.ne'
  have hprice' : q * pe ≤ (β : ℝ) * 3 ^ w := by
    have h := (div_le_iff₀ hS).mpr hprice
    change T * pe / S ≤ (β : ℝ) * 3 ^ w at h
    dsimp [q]
    nlinarith [h]
  have hbudget' : q * cB + q * jb ≤ 11 / 8 * (3 : ℝ) ^ w := by
    have h := (div_le_iff₀ hS).mpr hbudget
    change T * (cB + jb) / S ≤ 11 / 8 * (3 : ℝ) ^ w at h
    dsimp [q]
    nlinarith [h]
  obtain ⟨C', hm', hmean, h0', hch', hjump'⟩ :=
    chunk_scale_sizes_price C q hq0 hq1 hjump
  have hmean' : (∑ ω, C'.P ω * ∑ i, C'.size ω i) = T := hmean.trans hqS
  let C'' : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
      (bcrLevel2 β hβ (w + 1)).metric
      (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
      0 (q * cB) T ((β : ℝ) * 3 ^ w) 0 :=
    { C' with
      htotal := hmean'.ge
      hcost := by
        intro i ω₀ E bail
        refine (C'.hcost i ω₀ E bail).trans ?_
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (C'.hP ω).le
        unfold EvaderAlgorithm.bailCost
        split <;> linarith }
  refine ⟨q * cB, q * jb, mul_nonneg hq0 hcB, mul_nonneg hq0 hjb,
    hbudget', C'', ?_, ?_, ?_, ?_⟩
  · exact hmean'
  · exact h0' h0
  · exact hch' hch
  · exact hjump'
