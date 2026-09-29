-- Prove2me | solution 1 for mme_dwz_q6_112_table2_primary_hash_family_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:25:28.497803+00:00
-- url     : https://prove2.me/submissions/21c0d2ae-e32f-4a8f-b3a1-036489733f2e

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss

open MME Filter Topology

private theorem combineOuterMiddleBounds
    {Z B X A H e : ℝ}
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hX : 0 < X)
    (hA0 : 0 ≤ A) (he : 0 ≤ e)
    (hA : Z * e ≤ A)
    (hH : B * e ≤ 4 * X ^ 2 * H) :
    ((Z ^ 3 * B ^ 2) / (16 * X ^ 4)) * e ^ 5 ≤
      A ^ 3 * H ^ 2 := by
  have hA3 : (Z * e) ^ 3 ≤ A ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hZ he) hA 3
  have hB2 : (B * e) ^ 2 ≤ (4 * X ^ 2 * H) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hB he) hH 2
  have hraw :
      Z ^ 3 * B ^ 2 * e ^ 5 ≤
        16 * X ^ 4 * (A ^ 3 * H ^ 2) := by
    calc
      Z ^ 3 * B ^ 2 * e ^ 5 = (Z * e) ^ 3 * (B * e) ^ 2 := by ring
      _ ≤ A ^ 3 * (4 * X ^ 2 * H) ^ 2 :=
        mul_le_mul hA3 hB2 (by positivity) (by positivity)
      _ = 16 * X ^ 4 * (A ^ 3 * H ^ 2) := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 16 * X ^ 4)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hraw

/-!
The exact Table-2 `b = 21015 / 10^8` specialization of the finite
Salem--Spencer first hash used for the `(1,1,2)` component.

At source tensor power `m = 10^8 * t`, the primary-family convention uses
`m = 2*N`, so

* `N = 50,000,000*t`,
* `L = 21,015*t = b*m`, and
* `G = 49,978,985*t = ((1 - 2*b)/2)*m`.

The conclusion is purely combinatorial.  It constructs actual
`CWQ6PrimaryHashFamily` witnesses and exposes the two finite counts whose
product gives the Appendix-A `(1,1,2)` multinomial rate.  There is no tensor
restriction or tau-value premise in the statement.
-/
theorem solution :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t : ℕ in atTop,
        let N : ℕ := 50000000 * t
        let L : ℕ := 21015 * t
        let G : ℕ := 49978985 * t
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let loss : ℝ :=
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) * loss ≤ (A : ℝ) ∧
            (middle : ℝ) * loss ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
            ((((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
                  (16 * (Xcount : ℝ) ^ 4)) * loss ^ 5) ≤
              (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
  let scale : ℕ := 50000000
  let LAt : ℕ → ℕ := fun N => 21015 * (N / scale)
  let GAt : ℕ → ℕ := fun N => N - LAt N
  obtain ⟨C, hC, hfamilies⟩ :=
    mme_CW_q6_primary_hash_uniform_stars_sqrt_loss LAt GAt
  refine ⟨C, hC, ?_⟩
  have hscale : Tendsto (fun t : ℕ => scale * t) atTop atTop := by
    simpa [scale, nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ => x) atTop atTop).nsmul_atTop
        (by norm_num : 0 < (50000000 : ℕ)))
  have hpulled := hscale.eventually hfamilies
  filter_upwards [hpulled, eventually_gt_atTop 0] with t ht htpos
  have hL : LAt (scale * t) = 21015 * t := by
    simp [LAt, scale]
  have hG : GAt (scale * t) = 49978985 * t := by
    simp [GAt, LAt, scale]
    omega
  rw [hL, hG] at ht
  have hprofile :
      0 < 21015 * t ∧
        21015 * t + 49978985 * t = 50000000 * t ∧
        341 * (21015 * t) < 100 * (49978985 * t) := by
    constructor
    · positivity
    constructor <;> nlinarith
  have hexact := ht hprofile
  simp only [scale] at hexact
  rcases hexact with ⟨A, H, family, hHle, hA, hmiddle⟩
  refine ⟨A, H, family, hHle, hA, hmiddle, ?_⟩
  have hGleN : 49978985 * t ≤ 50000000 * t := by nlinarith
  have hXpos :
      0 < ((Nat.choose (50000000 * t) (49978985 * t) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hGleN
  apply combineOuterMiddleBounds
  · positivity
  · positivity
  · exact hXpos
  · positivity
  · exact (Real.exp_pos _).le
  · exact hA
  · exact hmiddle
