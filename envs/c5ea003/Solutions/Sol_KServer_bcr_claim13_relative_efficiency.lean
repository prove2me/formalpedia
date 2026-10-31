-- Prove2me | solution 1 for KServer.bcr_claim13_relative_efficiency
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T16:41:55.821677+00:00
-- url     : https://prove2.me/submissions/f3d311aa-ec64-4295-84f1-4cc62c6aa5ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_race_moment_construction
import Theorems.Thm_KServer_race_abs_moment_lower
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
        (α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)
          ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
        ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) * pe
          ≤ ((β : ℝ) * 3 ^ w) * (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
        ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) * (cB + jb)
          ≤ (11 / 8 * (3 : ℝ) ^ w) * (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
        (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
        (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
        C.DoobJumpBound jb  := by
  classical
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, Z, h2, h4, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_race_moment_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  have hw0 : 1 ≤ w := by
    by_contra hn
    have heq : w = 0 := by omega
    subst w
    norm_num at hw
    linarith
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw0
  have ha : 0 < α * (β : ℝ) := mul_pos hα (by exact_mod_cast hβ)
  have hr : 0 < Real.sqrt (α * (β : ℝ)) := Real.sqrt_pos.2 ha
  have hrsq := Real.sq_sqrt (le_of_lt ha)
  have hrsmall : Real.sqrt (α * (β : ℝ)) ≤ 1 / 1000 := by
    nlinarith [Real.sqrt_nonneg (α * (β : ℝ))]
  have ha_r : 9 * (α * (β : ℝ)) ≤ Real.sqrt (α * (β : ℝ)) / 100 := by
    have hh := mul_le_mul_of_nonneg_left hrsmall (le_of_lt hr)
    nlinarith
  have hmom := race_abs_moment_lower C.P Z (fun ω => le_of_lt (C.hP ω))
    (Real.sqrt (α * (β : ℝ)) * (w : ℝ)) (mul_pos hr (by linarith)) h2 h4
  have hgain : 3 * (α * (β : ℝ)) * ((w : ℝ) + 1) ^ 2 ≤
      3 * (α * (β : ℝ)) * (w : ℝ) ^ 2 + (∑ ω, C.P ω * |Z ω|) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right ha_r (show 0 ≤ (w : ℝ) by positivity)
    have hmul2 := mul_le_mul_of_nonneg_left hwR (le_of_lt ha)
    nlinarith
  have htarget : (α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1) ≤
      ∑ ω, C.P ω * ∑ i, C.size ω i := by
    have hh := mul_le_mul_of_nonneg_right hgain (show 0 ≤ (3 : ℝ) ^ w by positivity)
    calc
      _ = (3 * (α * (β : ℝ)) * ((w : ℝ) + 1) ^ 2) * 3 ^ w := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ ≤ _ := hh.trans hmass
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, htarget, ?_, ?_, h0, hch, hjump⟩
  · calc
      _ ≤ ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) *
          ((β : ℝ) * 3 ^ w) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left htarget
          (show 0 ≤ (β : ℝ) * 3 ^ w by positivity)
  · calc
      _ ≤ ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) *
          (11 / 8 * (3 : ℝ) ^ w) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left htarget
          (show 0 ≤ 11 / 8 * (3 : ℝ) ^ w by positivity)
