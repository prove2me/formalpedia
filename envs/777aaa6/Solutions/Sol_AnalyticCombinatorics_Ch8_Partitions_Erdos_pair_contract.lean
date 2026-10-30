-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.pair_contract
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:49:10.104743+00:00
-- url     : https://prove2.me/submissions/b2eb8a8b-37d8-41ef-8d15-d7cb283e46f5

import Mathlib

namespace AnalyticCombinatorics end AnalyticCombinatorics
namespace AnalyticCombinatorics.Ch8 end AnalyticCombinatorics.Ch8
namespace AnalyticCombinatorics.Ch8.Partitions end AnalyticCombinatorics.Ch8.Partitions
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos end AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin (File A): the deterministic overlap-contraction inequality

ChatGPT's recommended route to Fact B replaces entrance-distribution convergence by a finite-time
Doeblin oscillation contraction.  Its deterministic keystone is: if two probability vectors `p, q`
share a common mass `≥ δ` (overlap), then their averages of any function `f` of oscillation `≤ W`
differ by at most `(1 − δ)·W`.  This is pure nonnegative-sequence analysis — no probability theory.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Two sub-probability vectors of equal mass `m`, averaging a function valued in `[lo, lo+W]`,
differ by at most `m·W`. -/
lemma subprob_avg_diff {s : Finset ℕ} {a b f : ℕ → ℝ} {m lo W : ℝ}
    (ha : ∀ k ∈ s, 0 ≤ a k) (hb : ∀ k ∈ s, 0 ≤ b k)
    (ham : ∑ k ∈ s, a k = m) (hbm : ∑ k ∈ s, b k = m)
    (hf : ∀ k ∈ s, lo ≤ f k ∧ f k ≤ lo + W) :
    |∑ k ∈ s, a k * f k - ∑ k ∈ s, b k * f k| ≤ m * W := by
  have hshift : ∀ g : ℕ → ℝ, ∑ k ∈ s, g k = m →
      ∑ k ∈ s, g k * f k = ∑ k ∈ s, g k * (f k - lo) + m * lo := by
    intro g hg
    rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ s, g k * f k = g k * (f k - lo) + g k * lo),
      Finset.sum_add_distrib, ← Finset.sum_mul, hg]
  rw [hshift a ham, hshift b hbm]
  have hAlo : 0 ≤ ∑ k ∈ s, a k * (f k - lo) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (ha k hk) (by linarith [(hf k hk).1]))
  have hAhi : ∑ k ∈ s, a k * (f k - lo) ≤ m * W := by
    rw [← ham, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (by linarith [(hf k hk).2]) (ha k hk))
  have hBlo : 0 ≤ ∑ k ∈ s, b k * (f k - lo) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hb k hk) (by linarith [(hf k hk).1]))
  have hBhi : ∑ k ∈ s, b k * (f k - lo) ≤ m * W := by
    rw [← hbm, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (by linarith [(hf k hk).2]) (hb k hk))
  rw [show (∑ k ∈ s, a k * (f k - lo) + m * lo) - (∑ k ∈ s, b k * (f k - lo) + m * lo)
      = (∑ k ∈ s, a k * (f k - lo)) - (∑ k ∈ s, b k * (f k - lo)) by ring]
  rw [abs_le]
  constructor <;> linarith

/-- **Doeblin averaging contraction.** Probability vectors `p, q` with overlap `≥ δ`, averaging a
function `f` valued in `[lo, lo+W]`, differ by at most `(1−δ)·W`. -/
lemma doeblin_average_diff_bound {s : Finset ℕ} {p q f : ℕ → ℝ} {δ lo W : ℝ}
    (hpm : ∑ k ∈ s, p k = 1) (hqm : ∑ k ∈ s, q k = 1)
    (hov : δ ≤ ∑ k ∈ s, min (p k) (q k))
    (hf : ∀ k ∈ s, lo ≤ f k ∧ f k ≤ lo + W) (hW : 0 ≤ W) :
    |∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k| ≤ (1 - δ) * W := by
  set r : ℕ → ℝ := fun k => min (p k) (q k) with hr
  set m : ℝ := 1 - ∑ k ∈ s, r k with hm
  have hra : ∀ k ∈ s, 0 ≤ p k - r k := fun k _ => by simp only [hr]; linarith [min_le_left (p k) (q k)]
  have hrb : ∀ k ∈ s, 0 ≤ q k - r k := fun k _ => by simp only [hr]; linarith [min_le_right (p k) (q k)]
  have hma : ∑ k ∈ s, (p k - r k) = m := by rw [Finset.sum_sub_distrib, hpm, hm]
  have hmb : ∑ k ∈ s, (q k - r k) = m := by rw [Finset.sum_sub_distrib, hqm, hm]
  have hcancel : ∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k
      = ∑ k ∈ s, (p k - r k) * f k - ∑ k ∈ s, (q k - r k) * f k := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hcancel]
  have hkey := subprob_avg_diff hra hrb hma hmb hf
  have hmle : m ≤ 1 - δ := by rw [hm]; linarith [hov]
  calc |∑ k ∈ s, (p k - r k) * f k - ∑ k ∈ s, (q k - r k) * f k| ≤ m * W := hkey
    _ ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right hmle hW

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: the pairwise oscillation contraction

The core contraction step: two points `i, j` whose (iterated) transition laws `Q i ·`, `Q j ·` overlap
by `≥ δ` over a common support `T`, and which are each `η`-approximately `Q`-harmonic, satisfy
`|u i − u j| ≤ (1−δ)·W + 2η`, where `W` bounds the oscillation of `u` on `T` (via a band `[lo, lo+W]`).
This is the deterministic heart of the renewal oscillation contraction; the `δ` comes from the
finite-time Doeblin overlap (the remaining hard analytic input).  Opus-authored.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos in
theorem solution {u : ℕ → ℝ} {Q : ℕ → ℕ → ℝ} {i j : ℕ} {T : Finset ℕ} {δ η lo W : ℝ}
    (hQi_m : ∑ k ∈ T, Q i k = 1) (hQj_m : ∑ k ∈ T, Q j k = 1)
    (hov : δ ≤ ∑ k ∈ T, min (Q i k) (Q j k))
    (hband : ∀ k ∈ T, lo ≤ u k ∧ u k ≤ lo + W) (hW : 0 ≤ W)
    (hηi : |u i - ∑ k ∈ T, Q i k * u k| ≤ η)
    (hηj : |u j - ∑ k ∈ T, Q j k * u k| ≤ η) :
    |u i - u j| ≤ (1 - δ) * W + 2 * η := by
  have hmid : |∑ k ∈ T, Q i k * u k - ∑ k ∈ T, Q j k * u k| ≤ (1 - δ) * W :=
    doeblin_average_diff_bound hQi_m hQj_m hov hband hW
  have htri1 : |u i - u j|
      ≤ |u i - ∑ k ∈ T, Q i k * u k| + |∑ k ∈ T, Q i k * u k - u j| := abs_sub_le _ _ _
  have htri2 : |∑ k ∈ T, Q i k * u k - u j|
      ≤ |∑ k ∈ T, Q i k * u k - ∑ k ∈ T, Q j k * u k|
        + |∑ k ∈ T, Q j k * u k - u j| := abs_sub_le _ _ _
  have hηj' : |∑ k ∈ T, Q j k * u k - u j| ≤ η := by rw [abs_sub_comm]; exact hηj
  linarith [hmid, hηi, hηj', htri1, htri2]
