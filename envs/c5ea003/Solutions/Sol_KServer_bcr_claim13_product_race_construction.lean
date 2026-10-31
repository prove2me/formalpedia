-- Prove2me | solution 1 for KServer.bcr_claim13_product_race_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:48:11.307687+00:00
-- url     : https://prove2.me/submissions/d1bb98c1-8323-47fd-b684-a53c37ebf237
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_graded_sampler_construction
import Theorems.Thm_KServer_binary_read_trace_nonanticipation
open KServer

theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @NonnegChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ) (H : ℕ → C.Ω → ℕ) (B : ℕ → C.Ω → Bool)
          (d : ℕ) (p : Fin d → ℝ) (e : C.Ω ≃ (Fin d → Bool)) (I : ℕ → C.Ω → Fin d),
          (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧
          (∀ ω, C.P ω = ∏ i, if (e ω) i then p i else 1 - p i) ∧
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' →
            S j ω = S j ω' ∧ L j ω = L j ω' ∧ R j ω = R j ω') ∧
          (∀ j < N, ∀ ω, S (j + 1) ω =
            if B j ω then S j ω + L j ω else S j ω - R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' → I j ω = I j ω') ∧
          (∀ j < N, ∀ ω, p (I j ω) = R j ω / (L j ω + R j ω)) ∧
          (∀ j < N, ∀ ω, B j ω = (e ω) (I j ω)) ∧
          (∀ j < N, ∀ ω (b : Bool),
            H j (e.symm (Function.update (e ω) (I j ω) b)) = H j ω) ∧
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
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R, H, B, d, p, e, I, K, grade, choose,
    hpi, hprod, hzero, hlr, hknown, hupdate, hgrade, htrace, hread,
    hratio, hbit, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_graded_sampler_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R, H, B, d, p, e, I,
    hpi, hprod, hzero, hlr, hknown, hupdate, ?_, hratio, hbit, ?_,
    hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩
  · intro j hj ω ω' hh
    rw [hread j hj ω, hread j hj ω', (htrace j hj ω ω').mp hh]
  · intro j hj ω b
    have htime : K + j < K + N := Nat.add_lt_add_left hj K
    have hgi : grade (I j ω) = K + j := by
      rw [hread j hj ω]
      exact hgrade (K + j) htime _
    have hagree : ∀ i, grade i < K + j →
        (Function.update (e ω) (I j ω) b) i = (e ω) i := by
      intro i hi
      have hne : i ≠ I j ω := by
        intro heq
        rw [heq, hgi] at hi
        exact (Nat.lt_irrefl _ hi)
      simp [hne]
    have ht := binary_read_trace_nonanticipation grade choose (K + N) hgrade
      (K + j) (Nat.le_of_lt htime) (Function.update (e ω) (I j ω) b) (e ω) hagree
    apply (htrace j hj (e.symm (Function.update (e ω) (I j ω) b)) ω).mpr
    simpa only [e.apply_symm_apply] using ht
