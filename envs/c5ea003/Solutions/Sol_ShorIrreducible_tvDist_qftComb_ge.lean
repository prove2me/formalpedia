-- Prove2me | solution 1 for ShorIrreducible.tvDist_qftComb_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:54:09.218307+00:00
-- url     : https://prove2.me/submissions/cb64bdf8-e9e8-4dff-ac9e-375052956d39

-- Sol generated from Novelty/ShorQFTOutput.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutput
import Theorems.Thm_ShorIrreducible_card_multiples_range
import Theorems.Thm_ShorIrreducible_card_peakSet
import Theorems.Thm_ShorIrreducible_tvDist_ge_sum_sub

/-! # The QFT output of the comb: exactly `r` flat peaks, and why truncation fails

This file computes the *output* of the quantum Fourier transform on the periodic
comb `[x ≡ x₀ mod r]` of a register of size `Q = r * m`, and derives the
sampling-level obstruction to any classical emulation that keeps only
polynomially many amplitudes.

Main results:

* `combDFT_eq` : the Fourier sum of the comb,
  `∑_{t<m} ζ_Q^{(j + r t) y} = m ζ_Q^{j y}` if `m ∣ y` and `0` otherwise:
  the output is supported on the `r` multiples of `m = Q / r` and nowhere else;
* `norm_combDFT` : all `r` surviving amplitudes have the *same* modulus `m` —
  the output comb is flat, not "nearly a single basis state";
* `qftCombProb_apply` and `sum_qftCombProb` : the measured output distribution
  is uniform on those `r` frequencies;
* `tvDist_ge_sum_sub` and `tvDist_qftComb_ge` : **any** classical sampler whose
  output distribution is supported on a set `S` differs from the ideal Shor
  output distribution in total variation by at least `1 - |S| / r`; with
  `2 * |S| ≤ r` the distance is at least `1/2`
  (`tvDist_qftComb_ge_half`).  A truncated emulation fails catastrophically
  rather than approximately.
-/

open Finset
open scoped Real

open ShorIrreducible

/-! ## The Fourier transform of a comb -/








/-! ## The output distribution of Shor's algorithm -/




/-- The output distribution is a probability distribution: exactly `r` peaks of
weight `1 / r`. -/
theorem sum_qftCombProb {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ∑ y ∈ Finset.range (r * m), qftCombProb r m y = 1 := by
  classical
  simp only [qftCombProb]
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_range hm, nsmul_eq_mul]
  have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/-! ## Total-variation failure of any small-support sampler -/








open ShorIrreducible in
theorem solution{r m : ℕ} (hr : 0 < r) (hm : 0 < m) (q : Fin (r * m) → ℝ)
    (hq : ∑ y, q y = 1) (S : Finset (Fin (r * m))) (hsupp : ∀ y ∉ S, q y = 0) :
    1 - (S.card : ℝ) / r ≤ tvDist (fun y : Fin (r * m) => qftCombProb r m (y : ℕ)) q := by
  classical
  set p : Fin (r * m) → ℝ := fun y => qftCombProb r m (y : ℕ) with hp
  have hpsum : ∑ y, p y = 1 := by
    rw [hp, ← sum_qftCombProb hr hm, Fin.sum_univ_eq_sum_range (fun y => qftCombProb r m y)]
  set A : Finset (Fin (r * m)) := peakSet r m \ S with hA
  have hqA : ∀ y ∈ A, q y = 0 := by
    intro y hy
    exact hsupp y (Finset.mem_sdiff.mp hy).2
  have hpA : ∀ y ∈ A, p y = (r : ℝ)⁻¹ := by
    intro y hy
    have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
    rw [hp]
    simp only [qftCombProb, if_pos this]
  have hsum : ∑ y ∈ A, (p y - q y) = (A.card : ℝ) * (r : ℝ)⁻¹ := by
    rw [Finset.sum_congr rfl (fun y hy => by rw [hpA y hy, hqA y hy, sub_zero]),
      Finset.sum_const, nsmul_eq_mul]
  have hcard : (r : ℝ) ≤ (A.card : ℝ) + (S.card : ℝ) := by
    have hnat : r ≤ A.card + S.card := by
      calc r = (peakSet r m).card := (card_peakSet hm).symm
        _ ≤ (peakSet r m \ S).card + S.card := Finset.card_le_card_sdiff_add_card
        _ = A.card + S.card := by rw [hA]
    exact_mod_cast hnat
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hkey : 1 - (S.card : ℝ) / r ≤ ∑ y ∈ A, (p y - q y) := by
    rw [hsum, ← div_eq_mul_inv, le_div_iff₀ hrpos, sub_mul, one_mul,
      div_mul_cancel₀ _ hrpos.ne']
    linarith
  exact le_trans hkey (tvDist_ge_sum_sub hpsum hq A)
