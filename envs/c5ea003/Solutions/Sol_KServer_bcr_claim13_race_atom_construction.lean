-- Prove2me | solution 1 for KServer.bcr_claim13_race_atom_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:23:20.175608+00:00
-- url     : https://prove2.me/submissions/4d467235-5c78-4749-81f8-67ec888198c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_nonneg_race_construction
import Theorems.Thm_KServer_nonneg_chunk_positive_support
open KServer

private theorem filter_mass_of_expected_map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : Ω → ℝ) (Q : Ξ → ℝ) (e : Ω → Ξ)
    (h : ∀ f : Ξ → ℝ, (∑ ω, P ω * f (e ω)) = ∑ ξ, Q ξ * f ξ)
    (r : Ξ → Prop) [DecidablePred r] :
    (∑ ω ∈ Finset.univ.filter (fun ω => r (e ω)), P ω) =
      ∑ ξ ∈ Finset.univ.filter r, Q ξ := by
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using
    h (fun ξ => if r ξ then 1 else 0)

theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ) (H : ℕ → C.Ω → ℕ) (B : ℕ → C.Ω → Bool),
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' →
            S j ω = S j ω' ∧ L j ω = L j ω' ∧ R j ω = R j ω') ∧
          (∀ j < N, ∀ ω, S (j + 1) ω =
            if B j ω then S j ω + L j ω else S j ω - R j ω) ∧
          (∀ j < N, ∀ ω₀,
            (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀ ∧ B j ω = true), C.P ω) =
              (R j ω₀ / (L j ω₀ + R j ω₀)) *
                (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀), C.P ω)) ∧
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
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, D, N, S, L, R, H, B,
    hzero, hlr, hknown, hupdate, hbalance, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_nonneg_race_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  obtain ⟨C, e, hm, hP, hExp, hHist, hTotal, h0C, hchC, hjumpC⟩ :=
    nonneg_chunk_positive_support D h0 hch hjump
  have hsums (f : ℕ → D.Ω → ℝ) :
      (∑ j ∈ Finset.range N, ∑ ω, C.P ω * f j (e ω)) =
        ∑ j ∈ Finset.range N, ∑ ω, D.P ω * f j ω := by
    apply Finset.sum_congr rfl
    intro j _
    exact hExp (f j)
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, N,
    (fun j ω => S j (e ω)), (fun j ω => L j (e ω)), (fun j ω => R j (e ω)),
    (fun j ω => H j (e ω)), (fun j ω => B j (e ω)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp, hb, h0C, hchC, hjumpC⟩
  · intro ω
    exact hzero (e ω)
  · intro j hj ω
    exact hlr j hj (e ω)
  · intro j hj ω ω' hH
    exact hknown j hj (e ω) (e ω') hH
  · intro j hj ω
    exact hupdate j hj (e ω)
  · intro j hj ω₀
    rw [filter_mass_of_expected_map C.P D.P e hExp
        (fun ω => H j ω = H j (e ω₀) ∧ B j ω = true),
      filter_mass_of_expected_map C.P D.P e hExp
        (fun ω => H j ω = H j (e ω₀))]
    exact hbalance j hj (e ω₀)
  · dsimp only
    rw [hsums (fun j ω => L j ω * R j ω)]
    exact hvar
  · dsimp only
    rw [hsums (fun j ω => L j ω * R j ω *
      (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
        L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2))]
    exact hquartic
  · dsimp only
    rw [hExp (fun ω => |S N ω|), hTotal]
    exact hmass
