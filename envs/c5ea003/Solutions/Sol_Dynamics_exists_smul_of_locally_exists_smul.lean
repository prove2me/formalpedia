-- Prove2me | solution 1 for Dynamics.exists_smul_of_locally_exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T03:09:57.071276+00:00
-- url     : https://prove2.me/submissions/be5108f9-c53c-4117-bebe-2f61eb40de3a

import Mathlib

theorem solution {G S : Type*} [Group G] [MulAction G S]
    (P : ℝ → S) (delta : ℝ) (hd : 0 < delta)
    (hloc : ∀ t0 t1 : ℝ, |t0 - t1| < delta → ∃ g : G, P t0 = g • P t1) :
    ∀ t0 t1 : ℝ, ∃ g : G, P t0 = g • P t1 := by
  have key : ∀ n : ℕ, ∀ t0 t1 : ℝ, |t0 - t1| ≤ n * (delta / 2) →
      ∃ g : G, P t0 = g • P t1 := by
    intro n
    induction n with
    | zero =>
      intro t0 t1 hle
      have : t0 = t1 := by
        have h0 : |t0 - t1| ≤ 0 := by simpa using hle
        have := abs_nonneg (t0 - t1)
        have : t0 - t1 = 0 := by
          have habs : |t0 - t1| = 0 := le_antisymm h0 (abs_nonneg _)
          exact abs_eq_zero.mp habs
        linarith
      subst this
      exact ⟨1, by rw [one_smul]⟩
    | succ n ih =>
      intro t0 t1 hle
      set s : ℝ := t0 + (t1 - t0) / (n + 1) with hs
      have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 : |t0 - s| < delta := by
        have hval : t0 - s = -((t1 - t0) / ((n : ℝ) + 1)) := by rw [hs]; ring
        rw [hval, abs_neg, abs_div, abs_of_pos hnR, div_lt_iff₀ hnR, abs_sub_comm]
        push_cast at hle
        nlinarith [hle, hd, hnR, mul_pos hnR hd]
      have h2 : |s - t1| ≤ (n : ℝ) * (delta / 2) := by
        have hval : s - t1 = (t0 - t1) * ((n : ℝ) / ((n : ℝ) + 1)) := by
          rw [hs]; field_simp; ring
        have hfr : |((n : ℝ) / ((n : ℝ) + 1))| = (n : ℝ) / ((n : ℝ) + 1) :=
          abs_of_nonneg (by positivity)
        rw [hval, abs_mul, hfr]
        push_cast at hle
        have hnn : (0:ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
        calc |t0 - t1| * ((n : ℝ) / ((n : ℝ) + 1))
            ≤ (((n : ℝ) + 1) * (delta / 2)) * ((n : ℝ) / ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = (n : ℝ) * (delta / 2) := by field_simp
      obtain ⟨g1, hg1⟩ := hloc t0 s h1
      obtain ⟨g2, hg2⟩ := ih s t1 h2
      exact ⟨g1 * g2, by rw [hg1, hg2, mul_smul]⟩
  intro t0 t1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, |t0 - t1| ≤ n * (delta / 2) :=
    ⟨⌈|t0 - t1| / (delta / 2)⌉₊, by
      rw [← div_le_iff₀ (by positivity)]
      exact Nat.le_ceil _⟩
  exact key n t0 t1 hn
