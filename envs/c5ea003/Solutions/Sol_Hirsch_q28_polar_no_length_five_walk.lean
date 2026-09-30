-- Prove2me | solution 1 for Hirsch.q28_polar_no_length_five_walk
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T14:42:50.147553+00:00
-- url     : https://prove2.me/submissions/1389918c-3aaa-4a3e-8553-cf6f8cd4778e

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Theorems.Thm_Hirsch_q28_polar_no_length_three_between_links

open scoped RealInnerProductSpace
open Set Classical Hirsch

lemma inner_single' (i : Fin 5) (c : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪EuclideanSpace.single i c, x⟫ = c * x i := by
  simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) i c x

lemma inner_vec5 (x0 x1 x2 x3 x4 : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪vec5 x0 x1 x2 x3 x4, x⟫ =
      x0 * x 0 + x1 * x 1 + x2 * x 2 + x3 * x 3 + x4 * x 4 := by
  simp [vec5, inner_add_left, inner_single']

lemma vec5_last (x0 x1 x2 x3 x4 : ℝ) : vec5 x0 x1 x2 x3 x4 (4 : Fin 5) = x4 := by
  have h0 : (4 : Fin 5) ≠ 0 := by decide
  have h1 : (4 : Fin 5) ≠ 1 := by decide
  have h2 : (4 : Fin 5) ≠ 2 := by decide
  have h3 : (4 : Fin 5) ≠ 3 := by decide
  unfold vec5
  simp only [PiLp.add_apply]
  rw [PiLp.single_eq_of_ne (p := 2) h0, PiLp.single_eq_of_ne (p := 2) h1,
    PiLp.single_eq_of_ne (p := 2) h2, PiLp.single_eq_of_ne (p := 2) h3,
    PiLp.single_eq_same]
  simp

lemma vec5_zero (x0 x1 x2 x3 x4 : ℝ) : vec5 x0 x1 x2 x3 x4 (0 : Fin 5) = x0 := by
  have h1 : (1 : Fin 5) ≠ (0 : Fin 5) := by decide
  have h2 : (2 : Fin 5) ≠ (0 : Fin 5) := by decide
  have h3 : (3 : Fin 5) ≠ (0 : Fin 5) := by decide
  have h4 : (4 : Fin 5) ≠ (0 : Fin 5) := by decide
  unfold vec5
  simp only [PiLp.add_apply]
  simp [PiLp.single_eq_same, PiLp.single_eq_of_ne (p := 2) h1,
    PiLp.single_eq_of_ne (p := 2) h2, PiLp.single_eq_of_ne (p := 2) h3,
    PiLp.single_eq_of_ne (p := 2) h4]

lemma q28A_last (i : Fin 28) : q28A i (4 : Fin 5) = 1 ∨ q28A i (4 : Fin 5) = -1 := by
  unfold q28A
  split <;> simp [vec5_last]

lemma q28A_coord0_le (i : Fin 28) : |q28A i (0 : Fin 5)| ≤ 30 := by
  unfold q28A
  split <;> simp [vec5_zero] <;> norm_num

lemma inner_q28U (i : Fin 28) : ⟪q28A i, q28U⟫ = q28A i (4 : Fin 5) := by
  rw [real_inner_comm, q28U, inner_single', one_mul]

lemma inner_q28V (i : Fin 28) : ⟪q28A i, q28V⟫ = - q28A i (4 : Fin 5) := by
  rw [real_inner_comm, q28V, inner_single']
  ring

lemma q28U_mem : q28U ∈ Hpoly q28A q28B := by
  intro i
  have h := q28A_last i
  rw [q28B, inner_q28U]
  rcases h with h | h <;> simp [h]

lemma q28V_mem : q28V ∈ Hpoly q28A q28B := by
  intro i
  have h := q28A_last i
  rw [q28B, inner_q28V]
  rcases h with h | h <;> simp [h]

lemma q28U_ne_q28V : q28U ≠ q28V := by
  intro h
  have : (1 : ℝ) = -1 := by
    simpa [q28U, q28V, PiLp.single_eq_same] using
      congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z (4 : Fin 5)) h
  norm_num at this

lemma single_neg (i : Fin 5) (c : ℝ) :
    -EuclideanSpace.single i c = EuclideanSpace.single i (-c) := by
  ext j
  simp [PiLp.neg_apply, PiLp.single_apply]
  split_ifs <;> ring

lemma q28_small_coord_mem (ε : ℝ) (hε : |ε| ≤ 1 / 30) :
    EuclideanSpace.single (0 : Fin 5) ε ∈ Hpoly q28A q28B := by
  intro i
  have hin : ⟪q28A i, EuclideanSpace.single (0 : Fin 5) ε⟫ = ε * q28A i (0 : Fin 5) := by
    rw [real_inner_comm, inner_single']
  rw [hin, q28B]
  have hbd := q28A_coord0_le i
  have : ε * q28A i (0 : Fin 5) ≤ |ε| * |q28A i (0 : Fin 5)| := by
    simpa [abs_mul] using le_abs_self (ε * q28A i (0 : Fin 5))
  have : |ε| * |q28A i (0 : Fin 5)| ≤ |ε| * 30 :=
    mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
  have : |ε| * 30 ≤ 1 := by nlinarith
  linarith

lemma q28_apices_not_adj : ¬ Adj (Hpoly q28A q28B) q28U q28V := by
  intro hAdj
  obtain ⟨_, hex⟩ := hAdj
  let ε : ℝ := 1 / 30
  let x : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single 0 ε
  let y : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single 0 (-ε)
  have hxP : x ∈ Hpoly q28A q28B := q28_small_coord_mem ε (by norm_num [ε])
  have hyP : y ∈ Hpoly q28A q28B := q28_small_coord_mem (-ε) (by norm_num [ε])
  have hyx : y = -x := by
    simp [x, y, single_neg]
  have h0open : (0 : EuclideanSpace ℝ (Fin 5)) ∈ openSegment ℝ x y := by
    have h :=
      mem_openSegment_sub_add (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 5))
        (0 : EuclideanSpace ℝ (Fin 5)) x
    have hsub : (0 : EuclideanSpace ℝ (Fin 5)) - x = y := by
      simp [hyx, sub_eq_add_neg]
    rw [openSegment_symm, hsub, zero_add] at h
    exact h
  have h0seg : (0 : EuclideanSpace ℝ (Fin 5)) ∈ segment ℝ q28U q28V := by
    have hmid : midpoint ℝ q28U q28V = 0 := by
      apply PiLp.ext
      intro i
      fin_cases i <;>
        simp [midpoint_eq_smul_add, q28U, q28V, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, PiLp.single_eq_same,
          PiLp.single_eq_of_ne (p := 2)] <;> ring
    rw [← hmid]
    exact midpoint_mem_segment (𝕜 := ℝ) q28U q28V
  have hx_mem : x ∈ segment ℝ q28U q28V :=
    hex.left_mem_of_mem_openSegment hxP hyP h0seg h0open
  have hx0 : x (0 : Fin 5) = ε := by
    simp [x, PiLp.single_eq_same]
  have hz0 : ∀ z ∈ segment ℝ q28U q28V, z (0 : Fin 5) = 0 := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have h40 : (4 : Fin 5) ≠ 0 := by decide
    have hu0 : q28U (0 : Fin 5) = 0 := by
      simpa [q28U] using PiLp.single_eq_of_ne (p := 2) h40 (1 : ℝ)
    have hv0 : q28V (0 : Fin 5) = 0 := by
      simpa [q28V] using PiLp.single_eq_of_ne (p := 2) h40 (-1 : ℝ)
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu0, hv0]
  have : (ε : ℝ) = 0 := by
    simpa [hx0] using hz0 x hx_mem
  norm_num [ε] at this

theorem solution :
    ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
      ¬ (w 0 = q28U ∧ w 5 = q28V ∧
          ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by
  intro w ⟨hw0, hw5, hs⟩
  have hfirst : w 5 ≠ q28U := by
    rw [hw5]; exact q28U_ne_q28V.symm
  have hexs : ∃ i, i ≤ 5 ∧ w i ≠ q28U := ⟨5, by omega, hfirst⟩
  let s := Nat.find hexs
  have hs_le : s ≤ 5 := (Nat.find_spec hexs).1
  have hs_ne : w s ≠ q28U := (Nat.find_spec hexs).2
  have hs_min : ∀ i < s, w i = q28U := by
    intro i hi
    have hnot := Nat.find_min hexs hi
    have hile : i ≤ 5 := le_trans (Nat.le_of_lt hi) hs_le
    have : w i = q28U := by
      by_contra hne
      exact hnot ⟨hile, hne⟩
    exact this
  have hs_pos : 0 < s := by
    by_contra h
    have : s = 0 := by omega
    exact hs_ne (by simpa [this] using hw0)
  have hAdjU : Adj (Hpoly q28A q28B) q28U (w s) := by
    have hidx : s - 1 < 5 := by omega
    have hstep := hs (s - 1) hidx
    have hwprev : w (s - 1) = q28U := hs_min (s - 1) (Nat.sub_lt hs_pos (by omega))
    have hsucc : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.succ_le_of_lt hs_pos)
    rw [hwprev, hsucc] at hstep
    exact hstep.resolve_left (fun heq => hs_ne heq.symm)
  have hlast : w 0 ≠ q28V := by
    rw [hw0]; exact q28U_ne_q28V
  have hexr : ∃ i, i ≤ 5 ∧ w (5 - i) ≠ q28V := ⟨5, by omega, by simpa using hlast⟩
  let r := Nat.find hexr
  have hr_le : r ≤ 5 := (Nat.find_spec hexr).1
  have hr_ne : w (5 - r) ≠ q28V := (Nat.find_spec hexr).2
  have hr_min : ∀ i < r, w (5 - i) = q28V := by
    intro i hi
    have hnot := Nat.find_min hexr hi
    have hile : i ≤ 5 := le_trans (Nat.le_of_lt hi) hr_le
    by_contra hne
    exact hnot ⟨hile, hne⟩
  have hr_pos : 0 < r := by
    by_contra h
    have : r = 0 := by omega
    exact hr_ne (by simpa [this] using hw5)
  let t := 5 - r
  have ht_lt : t < 5 := by dsimp [t]; omega
  have hAdjV : Adj (Hpoly q28A q28B) (w t) q28V := by
    have hstep := hs t ht_lt
    have : t + 1 = 5 - (r - 1) := by dsimp [t]; omega
    have hr1 : r - 1 < r := Nat.sub_lt hr_pos (by omega)
    have hnext : w (t + 1) = q28V := by
      rw [this]
      exact hr_min (r - 1) hr1
    rw [hnext] at hstep
    exact hstep.resolve_left (fun heq => hr_ne (by
      have : t = 5 - r := rfl
      simpa [this] using heq))
  have hle_st : s ≤ t := by
    by_contra h
    have hlt : t < s := by omega
    have : w t = q28U := hs_min t hlt
    exact q28_apices_not_adj (by simpa [this] using hAdjV)
  have hlen : t - s ≤ 3 := by
    have : t ≤ 4 := by omega
    omega
  let w' : ℕ → EuclideanSpace ℝ (Fin 5) := fun j =>
    if j ≤ t - s then w (s + j) else w t
  have hw'0 : w' 0 = w s := by simp [w']
  have hw'3 : w' 3 = w t := by
    dsimp [w']
    split_ifs with hif
    · have : t - s = 3 := le_antisymm hlen hif
      have : s + 3 = t := by omega
      simp [this]
    · rfl
  have hw'step : ∀ j < 3, w' j = w' (j + 1) ∨
      Adj (Hpoly q28A q28B) (w' j) (w' (j + 1)) := by
    intro j hj
    by_cases h1 : j + 1 ≤ t - s
    · have h0 : j ≤ t - s := Nat.le_trans (Nat.le_succ j) h1
      have hstep := hs (s + j) (by omega)
      have hadd : s + j + 1 = s + (j + 1) := by omega
      simpa [w', h0, h1, hadd] using hstep
    · by_cases hjle : j ≤ t - s
      · have heq : j = t - s := by omega
        have hstay : w (s + j) = w t := by
          rw [heq, Nat.add_sub_of_le hle_st]
        simp [w', hjle, h1, hstay]
      · simp [w', hjle, h1]
  exact q28_polar_no_length_three_between_links (w s) (w t)
    ⟨hAdjU, hAdjV, w', hw'0, hw'3, hw'step⟩
