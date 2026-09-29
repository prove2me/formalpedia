-- Prove2me | solution 1 for NormalityConverse.hasBAdicIntervalFrequencies_of_cylinder_frequencies
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:32:25.504448+00:00
-- url     : https://prove2.me/submissions/291eea9f-dac7-4635-9943-6b4c2f39219e

import Mathlib
import Definitions.Def_NumberTheory_NormalityConverse

open NormalityConverse Filter Set Topology in
theorem solution {b : ℕ} {u : ℕ → ℝ} (h : HasBAdicCylinderFrequencies b u) :
    HasBAdicIntervalFrequencies b u := by
  obtain ⟨hb, hcyl⟩ := h
  refine ⟨hb, fun k A C hAC hC => ?_⟩
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  -- an aligned interval of `m + 1` cells, by induction on `m`
  have H : ∀ m : ℕ, A + (m + 1) ≤ b ^ k →
      Tendsto (empiricalFrequency (fun n => u n ∈
        Ico ((A : ℝ) / (b : ℝ) ^ k) (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)))
        atTop (𝓝 (((m : ℝ) + 1) / (b : ℝ) ^ k)) := by
    intro m
    induction m with
    | zero =>
      intro hle
      have h1 := hcyl k A (by omega)
      have e1 : ((A + (0 + 1) : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
      have e2 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
      rw [e1, e2]
      exact h1
    | succ m ih =>
      intro hle
      have h1 := ih (by omega)
      have h2 := hcyl k (A + (m + 1)) (by omega)
      have ec : ((A + (m + 1 + 1) : ℕ) : ℝ) = ((A + (m + 1) : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      rw [ec]
      have hle1 : (A : ℝ) / (b : ℝ) ^ k ≤ ((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k :=
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : A ≤ A + (m + 1))) hbk.le
      have hle2 : ((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k
          ≤ (((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k :=
        div_le_div_of_nonneg_right (by linarith) hbk.le
      -- the frequency of the longer interval splits over its last cell
      have hsplit : ∀ N, empiricalFrequency (fun n => u n ∈
            Ico ((A : ℝ) / (b : ℝ) ^ k) ((((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k)) N
          = empiricalFrequency (fun n => u n ∈
              Ico ((A : ℝ) / (b : ℝ) ^ k) (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)) N
            + empiricalFrequency (fun n => u n ∈
              Ico (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)
                ((((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k)) N := by
        intro N
        unfold empiricalFrequency
        rw [← add_div]
        congr 1
        have hfilt : (Finset.range N).filter (fun n => u n ∈
              Ico ((A : ℝ) / (b : ℝ) ^ k) ((((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k))
            = (Finset.range N).filter (fun n => u n ∈
                Ico ((A : ℝ) / (b : ℝ) ^ k) (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k))
              ∪ (Finset.range N).filter (fun n => u n ∈
                Ico (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)
                  ((((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k)) := by
          rw [← Finset.filter_or]
          apply Finset.filter_congr
          intro n _
          rw [← Set.mem_union, Set.Ico_union_Ico_eq_Ico hle1 hle2]
        have hdisj : Disjoint ((Finset.range N).filter (fun n => u n ∈
                Ico ((A : ℝ) / (b : ℝ) ^ k) (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)))
              ((Finset.range N).filter (fun n => u n ∈
                Ico (((A + (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ k)
                  ((((A + (m + 1) : ℕ) : ℝ) + 1) / (b : ℝ) ^ k))) := by
          rw [Finset.disjoint_filter]
          intro n _ hn1 hn2
          exact absurd hn2.1 (not_le.2 hn1.2)
        rw [hfilt, Finset.card_union_of_disjoint hdisj]
        push_cast
        ring
      have h3 := (h1.add h2).congr (fun N => (hsplit N).symm)
      have e : ((m : ℝ) + 1) / (b : ℝ) ^ k + 1 / (b : ℝ) ^ k
          = (((m + 1 : ℕ) : ℝ) + 1) / (b : ℝ) ^ k := by
        push_cast
        ring
      rw [e] at h3
      exact h3
  obtain ⟨m, rfl⟩ : ∃ m, C = A + (m + 1) := ⟨C - A - 1, by omega⟩
  have e : (((A + (m + 1) : ℕ) : ℝ) - A) / (b : ℝ) ^ k = ((m : ℝ) + 1) / (b : ℝ) ^ k := by
    push_cast
    ring
  rw [e]
  exact H m hC
