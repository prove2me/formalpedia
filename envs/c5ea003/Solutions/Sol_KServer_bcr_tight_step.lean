-- Prove2me | solution 1 for KServer.bcr_tight_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T11:08:21.868964+00:00
-- url     : https://prove2.me/submissions/103549fd-d557-44e5-9d5b-ee9502acc0e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_tight_subchunks
import Theorems.Thm_KServer_chunk_combining_zero_floor

open KServer

/-- The arithmetic of the regrouping: if the expected total is `A · y` with
`A > 64`, if the chunk count `M` is the ceiling of `A`, and if the slack
`cB + jbS` of the subchunk system is at most `11/24 · y`, then the mean chunk
mass `A·y/M` sits in the window `[y/2 + slack, 3y/2 - slack]` and the escape
price budget `2 · 64 · x` covers the regrouping overhead. -/
theorem regroup_window_arith (A y x cB jbS : ℝ) (M : ℕ)
    (hxy : y = 3 * x) (hx0 : 0 < x)
    (hA64 : 64 < A) (hAM : A ≤ (M : ℝ)) (hMA : (M : ℝ) < A + 1)
    (hs : cB + jbS ≤ 11 / 8 * x) :
    y / 2 ≤ A * y / (M : ℝ) - (cB + jbS) ∧
    A * y / (M : ℝ) + (cB + jbS) ≤ 3 * y / 2 ∧
    (64 : ℝ) * x + (A * y / (M : ℝ) + (cB + jbS)) ≤ 64 * y := by
  have hy0 : 0 < y := by rw [hxy]; linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (by linarith) hAM
  have hup : A * y / (M : ℝ) ≤ y := by
    rw [div_le_iff₀ hMpos]
    nlinarith
  have hdown : (23 / 24) * y ≤ A * y / (M : ℝ) := by
    rw [le_div_iff₀ hMpos]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- One level of BCR's Lemma 12 at the tight escape price, reduced to
Claim 13 (`KServer.bcr_claim13_tight_subchunks`) and the zero-floor
regrouping (`KServer.chunk_combining_zero_floor`). -/
theorem solution :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ β : ℕ, ∃ hβ : 0 < β, 2 ≤ β ∧
      ∀ w : ℕ, 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2 →
        BCRInductiveChunksTight α β hβ w →
        BCRInductiveChunksTight α β hβ (w + 1) := by
  refine ⟨1 / 10 ^ 8, by norm_num, by norm_num, 64, by norm_num, by norm_num, ?_⟩
  intro w hw hC
  obtain ⟨cB, jbS, hcB0, hjb0, hs, C, hE, h0, hch, hjb⟩ :=
    bcr_claim13_tight_subchunks (1 / 10 ^ 8) (by norm_num) (by norm_num)
      64 (by norm_num) (by norm_num) (by norm_num) w hw hC
  have hx0 : (0 : ℝ) < (3 : ℝ) ^ w := by positivity
  have hpow : (3 : ℝ) ^ (w + 1) = 3 * (3 : ℝ) ^ w := by rw [pow_succ]; ring
  have hA64 : (64 : ℝ) < 1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 := by
    have h : (1 : ℝ) < 1 / 10 ^ 8 * ((w + 1 : ℕ) : ℝ) ^ 2 := hw
    push_cast
    push_cast at h
    nlinarith
  have hA0 : (0 : ℝ) < 1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 := by
    linarith
  have hAM : 1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2
      ≤ ((⌈1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hMA : ((⌈1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2⌉₊ : ℕ) : ℝ)
      < 1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 + 1 :=
    Nat.ceil_lt_add_one hA0.le
  have hM0 : 0 < ⌈1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2⌉₊ := by
    have : (0 : ℝ) < ((⌈1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2⌉₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le hA0 hAM
    exact_mod_cast this
  obtain ⟨hlo, hhi, hpr⟩ :=
    regroup_window_arith (1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2)
      ((3 : ℝ) ^ (w + 1)) ((3 : ℝ) ^ w) cB jbS
      ⌈1 / 10 ^ 8 * ((64 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2⌉₊
      hpow hx0 hA64 hAM hMA hs
  obtain ⟨C', hm', h0', hch'⟩ :=
    chunk_combining_zero_floor C h0 hch hjb hjb0 hcB0 hM0
      (cLo' := (3 : ℝ) ^ (w + 1) / 2) (cHi' := 3 * (3 : ℝ) ^ (w + 1) / 2)
      (p' := ((64 : ℕ) : ℝ) * (3 : ℝ) ^ (w + 1)) (by positivity)
      (by rw [hE]; exact hlo) (by rw [hE]; exact hhi)
      (by rw [hE]; push_cast; push_cast at hpr; linarith)
  exact ⟨_, C', hm', le_refl _, h0', hch'⟩
