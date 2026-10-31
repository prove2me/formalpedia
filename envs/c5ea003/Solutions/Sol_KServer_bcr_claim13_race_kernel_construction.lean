-- Prove2me | solution 1 for KServer.bcr_claim13_race_kernel_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:05:31.91006+00:00
-- url     : https://prove2.me/submissions/5e710258-0e72-4a40-b959-2af81eb8e5c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_race_atom_construction
import Theorems.Thm_KServer_binary_kernel_of_atom_balance
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
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ),
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ f : ℝ → ℝ,
            (∑ ω, C.P ω * f (S (j + 1) ω)) =
              ∑ ω, C.P ω * (R j ω / (L j ω + R j ω) * f (S j ω + L j ω) +
                L j ω / (L j ω + R j ω) * f (S j ω - R j ω))) ∧
          (Real.sqrt (α * β) * (w : ℝ)) ^ 2 / 4 ≤
            (∑ j ∈ Finset.range N, ∑ ω, C.P ω * (L j ω * R j ω)) ∧
          (∑ j ∈ Finset.range N, ∑ ω, C.P ω *
            (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
              L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2))) ≤
            4 * (Real.sqrt (α * β) * (w : ℝ)) ^ 4 ∧
          (3 * (α * β) * (w : ℝ) ^ 2 + (∑ ω, C.P ω * |S N ω|) / 2) * 3 ^ w
            ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
          pe ≤ (β : ℝ) * 3 ^ w ∧
          cB + jb ≤ 11 / 8 * (3 : ℝ) ^ w ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
          (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
          C.DoobJumpBound jb  := by
  classical
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R, H, B,
    hzero, hlr, hknown, hupdate, hbalance, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_race_atom_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R,
    hzero, hlr, ?_, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩
  intro j hj f
  have hmeas : ∀ ω ω', H j ω = H j ω' →
      (S j ω + L j ω) = (S j ω' + L j ω') ∧
      (S j ω - R j ω) = (S j ω' - R j ω') ∧
      (R j ω / (L j ω + R j ω)) = (R j ω' / (L j ω' + R j ω')) := by
    intro ω ω' hH
    obtain ⟨hS, hL, hR⟩ := hknown j hj ω ω' hH
    rw [hS, hL, hR]
    exact ⟨rfl, rfl, rfl⟩
  have hratio (ω : C.Ω) : 1 - R j ω / (L j ω + R j ω) = L j ω / (L j ω + R j ω) := by
    have hden := ne_of_gt (hlr j hj ω).2.2
    field_simp
    ring
  calc
    _ = ∑ ω, C.P ω * f (if B j ω then S j ω + L j ω else S j ω - R j ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hupdate j hj ω]
    _ = ∑ ω, C.P ω * ((R j ω / (L j ω + R j ω)) * f (S j ω + L j ω) +
          (1 - R j ω / (L j ω + R j ω)) * f (S j ω - R j ω)) :=
      binary_kernel_of_atom_balance C.P (H j) (B j)
        (fun ω => S j ω + L j ω) (fun ω => S j ω - R j ω)
        (fun ω => R j ω / (L j ω + R j ω)) hmeas (hbalance j hj) f
    _ = _ := by simp_rw [hratio]
