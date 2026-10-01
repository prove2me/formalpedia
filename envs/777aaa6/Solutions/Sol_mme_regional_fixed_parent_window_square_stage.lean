-- Prove2me | solution 1 for mme_regional_fixed_parent_window_square_stage
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T20:02:44.641507+00:00
-- url     : https://prove2.me/submissions/f36d03ef-7861-4c38-b690-d6918826a0df

import Theorems.Thm_mme_graded_band_part_stage
import Theorems.Thm_mme_regional_parent_mixture_lipschitz
import Theorems.Thm_mme_parent_mixture_scale

open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization
  MME.DWZProfiledRegional
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Equal cell masses turn a relative count error into a frequency error,
including cells of mass zero. -/
private theorem frequency_close_of_count_close {C W : Type*} [Fintype W]
    (mu nu : C → W → ℕ) (delta : ℝ) (hd : 0 ≤ delta)
    (hm : ∀ c, ∑ w, mu c w = ∑ w, nu c w)
    (hc : ∀ c w, |(mu c w : ℝ) - (nu c w : ℝ)| ≤
      delta * ((∑ z, nu c z : ℕ) : ℝ)) :
    ∀ c w, |cellFrequency mu c w - cellFrequency nu c w| ≤ delta := by
  intro c w
  by_cases hz : ∑ z, nu c z = 0
  · simp [cellFrequency, hm c, hz, hd]
  · have hp : 0 < ((∑ z, nu c z : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    simp only [cellFrequency, hm c, ← sub_div, abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (hc c w)

/-- The band tolerance tends to zero along square scales, with an elementary
uniform threshold. -/
private theorem square_band_tolerance (A eps : ℝ) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → 0 < k ∧
      Real.sqrt (A * ((Nat.sqrt (k ^ 2) + 2 : ℕ) : ℝ) / (k ^ 2 : ℕ)) < eps / 2 := by
  obtain ⟨b, hb⟩ := exists_nat_gt (12 * A / eps ^ 2)
  refine ⟨max b 1, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := (le_max_right b 1).trans hk
  have hkpos : 0 < k := by omega
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hkpos
  have hkR1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlarge : 12 * A / eps ^ 2 < (k : ℝ) :=
    hb.trans_le (Nat.cast_le.mpr ((le_max_left b 1).trans hk))
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hlarge' : 12 * A < (k : ℝ) * eps ^ 2 := (div_lt_iff₀ he2).mp hlarge
  refine ⟨hkpos, ?_⟩
  rw [Nat.sqrt_eq']
  push_cast
  apply (Real.sqrt_lt' (by linarith : 0 < eps / 2)).mpr
  apply (div_lt_iff₀ (sq_pos_of_pos hkR)).mpr
  have hnum : A * ((k : ℝ) + 2) ≤ 3 * A * k := by nlinarith
  have hstrict : 3 * A * (k : ℝ) < (eps / 2) ^ 2 * (k : ℝ) ^ 2 := by
    have := mul_lt_mul_of_pos_right hlarge' hkR
    nlinarith
  exact hnum.trans_lt hstrict

/-- A fixed finite position coefficient is absorbed by a cubic polynomial in
the square-scale parameter. -/
private theorem square_position_bound {R : ℕ} (n : Fin R → ℕ) (k : ℕ)
    (hk : 2 * ∑ r, n r ≤ k) :
    Fintype.card (Position (fun r ↦ k ^ 2 * n r)) + 1 ≤ (k + 1) ^ 3 := by
  classical
  have hcard : Fintype.card (Position (fun r ↦ k ^ 2 * n r)) =
      (2 * ∑ r, n r) * k ^ 2 := by
    simp only [Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    rw [show (∑ r, k ^ 2 * n r * 2) = (2 * ∑ r, n r) * k ^ 2 by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring]
  rw [hcard]
  have := Nat.mul_le_mul_right (k ^ 2) hk
  nlinarith

/-- Generic recursive transition into a prescribed fixed parent window.
At `ell = 3`, this is the local level-four-to-level-three interface. -/
theorem solution {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ s, m r s = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i s, ∑ w, mu i s w = m s.1 s.2 + m s.1 (complement (htotal s.1) s.2))
    (rate eps : ℝ) (hr0 : 0 ≤ rate) (hr : rate < regionalRate htotal n m mu)
    (heps : 0 < eps)
    (center : Fin 3 → Fin R → (Fin 2 → CompleteSplit.CompleteWord ell) → ℝ)
    (hcenter : ∀ i r w, center i r w = parentMixture htotal n m (mu i) r w) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      0 < k ∧ ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ k ^ 2 * n r),
      a ∈ RecursiveXHash.target (n := fun r ↦ k ^ 2 * n r) (fun r s ↦ k ^ 2 * m r s) →
      ∃ D : LogPartStageG (lenAt n (k ^ 2) * 2 ^ (ell - 1)) ell
        (fun i x ↦
          let f := ProfiledCW.split (positionsAt n (k ^ 2)) rfl x
          ParentGraded parent (fun r ↦ k ^ 2 * n r) i f ∧
          ∀ r w, |(Fintype.card {t : Fin (k ^ 2 * n r) // ∀ h, f ⟨r,t,h⟩ = w h} : ℝ) /
            (k ^ 2 * n r : ℕ) - center i r w| < eps)
        (fun i y ↦
          let f := ProfiledCW.split (positionsAt n (k ^ 2)) rfl y
          let hist := count (fullCell htotal a) f
          Graded htotal i a f ∧
          (∀ s, ∑ w, hist s w = ∑ w, k ^ 2 * mu i s w) ∧
          ∀ s w, |(hist s w : ℝ) - ((k ^ 2 * mu i s w : ℕ) : ℝ)| ≤
            delta * ((∑ z, k ^ 2 * mu i s z : ℕ) : ℝ)),
        D.types ≤ (k + 1) ^
          (9 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
            Fintype.card (CompleteSplit.CompleteWord ell)) ∧ D.rate = rate * k ^ 2 := by
  classical
  obtain ⟨eta, heta, hband⟩ :=
    mme_graded_band_part_stage parent htotal n hn hR m hm mu hmass rate hr0 hr
  let delta : ℝ := min eta (eps / 8)
  have hd : 0 < delta := lt_min heta (by linarith)
  have hde : delta ≤ eta := min_le_left _ _
  have hdeps : delta ≤ eps / 8 := min_le_right _ _
  obtain ⟨b, hb⟩ := (eventually_atTop.1 hband)
  obtain ⟨q, hq⟩ := square_band_tolerance
    (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2))
    eps (by positivity) heps
  refine ⟨delta, hd, max (max b q) (2 * ∑ r, n r), ?_⟩
  intro k hk
  have hb' : b ≤ k := (le_max_left b q).trans ((le_max_left _ _).trans hk)
  have hq' : q ≤ k := (le_max_right b q).trans ((le_max_left _ _).trans hk)
  have hcoeff : 2 * ∑ r, n r ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hkpos, htolerance⟩ := hq k hq'
  have hspos : 0 < k ^ 2 := pow_pos hkpos _
  have hbk : b ≤ k ^ 2 := hb'.trans (by nlinarith)
  refine ⟨hkpos, ?_⟩
  intro a ha
  let good : Fin 3 → (Cell (2 * 2 ^ (ell - 1)) R parent →
      CompleteSplit.CompleteWord ell → ℕ) → Prop := fun i hist ↦
    (∀ s, ∑ w, hist s w = ∑ w, k ^ 2 * mu i s w) ∧
    ∀ s w, |(hist s w : ℝ) - ((k ^ 2 * mu i s w : ℕ) : ℝ)| ≤
      delta * ((∑ z, k ^ 2 * mu i s z : ℕ) : ℝ)
  have hgood : ∀ i hist, good i hist →
      (∀ s, ∑ w, hist s w = ∑ w, k ^ 2 * mu i s w) ∧
      ∀ s w, |(hist s w : ℝ) - ((k ^ 2 * mu i s w : ℕ) : ℝ)| ≤
        eta * ((∑ z, k ^ 2 * mu i s z : ℕ) : ℝ) := by
    intro i hist hh
    refine ⟨hh.1, ?_⟩
    intro s w
    exact (hh.2 s w).trans (mul_le_mul_of_nonneg_right hde (Nat.cast_nonneg _))
  have hsource : ∀ hist : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent →
      CompleteSplit.CompleteWord ell → ℕ, (∀ i, good i (hist i)) → ∀ i x,
      ParentGraded parent (fun r ↦ k ^ 2 * n r) i
        (ProfiledCW.split (positionsAt n (k ^ 2)) rfl x) →
      parentTypical htotal (fun r ↦ k ^ 2 * n r) (fun r s ↦ k ^ 2 * m r s) (hist i)
        (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
          ((Nat.sqrt (k ^ 2) + 2 : ℕ) : ℝ) / (k ^ 2 : ℕ)))
        (ProfiledCW.split (positionsAt n (k ^ 2)) rfl x) →
      ParentGraded parent (fun r ↦ k ^ 2 * n r) i
        (ProfiledCW.split (positionsAt n (k ^ 2)) rfl x) ∧
      ∀ r w, |(Fintype.card {t : Fin (k ^ 2 * n r) // ∀ h,
        (ProfiledCW.split (positionsAt n (k ^ 2)) rfl x) ⟨r,t,h⟩ = w h} : ℝ) /
        (k ^ 2 * n r : ℕ) - center i r w| < eps := by
    intro hist hh i x hg ht
    have hscaled : ∀ r, ∑ s, k ^ 2 * m r s = k ^ 2 * n r := by
      intro r
      rw [← Finset.mul_sum, hm r]
    have hclose := frequency_close_of_count_close (hist i)
      (fun s w ↦ k ^ 2 * mu i s w) delta hd.le (hh i).1 (hh i).2
    have htyp := (mme_regional_parent_mixture_lipschitz htotal
      (fun r ↦ k ^ 2 * n r) (fun r s ↦ k ^ 2 * m r s) hscaled
      (hist i) (fun s w ↦ k ^ 2 * mu i s w) delta hd.le hclose).2 _ _ ht
    refine ⟨hg, ?_⟩
    intro r w
    have ht' := htyp r w
    rw [mme_parent_mixture_scale htotal n m (mu i) (k ^ 2) hspos r w,
      ← hcenter i r w] at ht'
    have hbudget : Real.sqrt (8 * (25 * (R : ℝ) *
        (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
        ((Nat.sqrt (k ^ 2) + 2 : ℕ) : ℝ) / (k ^ 2 : ℕ)) + 2 * delta < eps := by
      linarith only [htolerance, hdeps, heps]
    simpa only [Fintype.card_eq_nat_card] using ht'.trans hbudget
  obtain ⟨D, htypes, hrate⟩ := hb (k ^ 2) hbk a ha good hgood _ hsource
  refine ⟨D, ?_, by simpa only [Nat.cast_pow] using hrate⟩
  have hpoly := Nat.pow_le_pow_left (square_position_bound n k hcoeff)
    (3 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
      Fintype.card (CompleteSplit.CompleteWord ell))
  apply htypes.trans
  simpa only [← pow_mul, show 3 * (3 * Fintype.card
    (Cell (2 * 2 ^ (ell - 1)) R parent) * Fintype.card (CompleteSplit.CompleteWord ell)) =
      9 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
        Fintype.card (CompleteSplit.CompleteWord ell) by ring] using hpoly

