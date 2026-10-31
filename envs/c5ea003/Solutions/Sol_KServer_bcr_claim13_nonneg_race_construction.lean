-- Prove2me | solution 1 for KServer.bcr_claim13_nonneg_race_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:34:11.1122+00:00
-- url     : https://prove2.me/submissions/ae770c57-7e6a-4ec0-8ae5-41aac19d6aff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_bcr_claim13_product_race_construction
import Theorems.Thm_KServer_bernoulli_fresh_coordinate
open KServer

private theorem filter_mass_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (P : Ω → ℝ) (A : Ξ → Prop) [DecidablePred A] :
    (∑ ω ∈ Finset.univ.filter (fun ω => A (e ω)), P ω) =
      ∑ x ∈ Finset.univ.filter A, P (e.symm x) := by
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv e
  intro ω
  simp only [e.symm_apply_apply]

theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @NonnegChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
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
  obtain ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R, H, B, d, p, e, I,
    hpi, hprod, hzero, hlr, hknown, hupdate, hI, hratio, hbit, hfresh,
    hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩ :=
    bcr_claim13_product_race_construction α hα hα1 β hβ hβ2 hsmall w hw hC
  refine ⟨cB, jb, pe, hcB, hjb, hpe, C, N, S, L, R, H, B,
    hzero, hlr, hknown, hupdate, ?_, hvar, hquartic, hmass, hp, hb, h0, hch, hjump⟩
  intro j hj ω₀
  let i : Fin d := I j ω₀
  let A : (Fin d → Bool) → Prop := fun x => H j (e.symm x) = H j ω₀
  have hstable : ∀ x, A x → A (Function.update x i (!(x i))) := by
    intro x hx
    have hi : I j (e.symm x) = i := hI j hj (e.symm x) ω₀ hx
    have hh := hfresh j hj (e.symm x) (!(x i))
    rw [e.apply_symm_apply, hi] at hh
    exact hh.trans hx
  have hprod' (x : Fin d → Bool) : C.P (e.symm x) = ∏ k, if x k then p k else 1 - p k := by
    simpa only [e.apply_symm_apply] using hprod (e.symm x)
  have hlaw := (bernoulli_fresh_coordinate p hpi (fun x => C.P (e.symm x)) hprod').2.2 i A hstable
  have hpred (ω : C.Ω) : (H j ω = H j ω₀ ∧ B j ω = true) ↔
      (A (e ω) ∧ (e ω) i = true) := by
    have hA : A (e ω) ↔ H j ω = H j ω₀ := by simp [A]
    rw [hA]
    by_cases hh : H j ω = H j ω₀
    · have hi : I j ω = i := hI j hj ω ω₀ hh
      rw [hbit j hj ω, hi]
    · simp [hh]
  have hleft : (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀ ∧ B j ω = true), C.P ω) =
      ∑ x ∈ Finset.univ.filter (fun x => A x ∧ x i = true), C.P (e.symm x) := by
    calc
      _ = ∑ ω ∈ Finset.univ.filter (fun ω => A (e ω) ∧ (e ω) i = true), C.P ω := by
        apply Finset.sum_congr
        · ext ω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hpred ω
        · intro _ _
          rfl
      _ = _ := filter_mass_equiv e C.P (fun x => A x ∧ x i = true)
  have hmassA : (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀), C.P ω) =
      ∑ x ∈ Finset.univ.filter A, C.P (e.symm x) := by
    have hh := filter_mass_equiv e C.P A
    simpa only [A, e.symm_apply_apply] using hh
  rw [hleft, hmassA]
  change _ = _
  rw [← hratio j hj ω₀]
  exact hlaw
