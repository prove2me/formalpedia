-- Prove2me | solution 1 for Hirsch.five_spindle_length_six
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T13:49:01.77803+00:00
-- url     : https://prove2.me/submissions/7182a48b-243d-41a8-8a06-4b6211bc92bc

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Theorems.Thm_Hirsch_q28_polar_no_length_five_walk

open scoped RealInnerProductSpace
open Set Hirsch

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

lemma q28A_last (i : Fin 28) : q28A i (4 : Fin 5) = 1 ∨ q28A i (4 : Fin 5) = -1 := by
  unfold q28A
  split <;> simp [vec5_last]

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

lemma q28_xor (i : Fin 28) :
    (⟪q28A i, q28U⟫ = q28B i) ↔ ⟪q28A i, q28V⟫ ≠ q28B i := by
  have h := q28A_last i
  simp [q28B, inner_q28U, inner_q28V]
  rcases h with h | h <;> simp [h] <;> norm_num

lemma q28A_0 : q28A 0 = vec5 18 0 0 0 1 := rfl
lemma q28A_1 : q28A 1 = vec5 (-18) 0 0 0 1 := rfl
lemma q28A_2 : q28A 2 = vec5 0 0 30 0 1 := rfl
lemma q28A_3 : q28A 3 = vec5 0 0 (-30) 0 1 := rfl
lemma q28A_4 : q28A 4 = vec5 0 0 0 30 1 := rfl
lemma q28A_5 : q28A 5 = vec5 0 0 0 (-30) 1 := rfl
lemma q28A_6 : q28A 6 = vec5 0 5 0 25 1 := rfl
lemma q28A_16 : q28A 16 = vec5 0 30 0 0 (-1) := rfl
lemma q28A_17 : q28A 17 = vec5 0 (-30) 0 0 (-1) := rfl
lemma q28A_18 : q28A 18 = vec5 30 0 0 0 (-1) := rfl
lemma q28A_19 : q28A 19 = vec5 (-30) 0 0 0 (-1) := rfl

lemma coord_abs_le_one {x : EuclideanSpace ℝ (Fin 5)} (hx : x ∈ Hpoly q28A q28B) (i : Fin 5) :
    |x i| ≤ 1 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have h5 := hx 5
  have h16 := hx 16
  have h17 := hx 17
  have h18 := hx 18
  have h19 := hx 19
  simp only [q28B, q28A_0, q28A_1, q28A_2, q28A_3, q28A_4, q28A_5, q28A_16, q28A_17,
    q28A_18, q28A_19, inner_vec5, zero_mul, one_mul, add_zero, neg_mul] at h0 h1 h2 h3 h4 h5 h16 h17 h18 h19
  have hx4u : x 4 ≤ 1 := by linarith
  have hx4l : -x 4 ≤ 1 := by linarith
  have hx0u : x 0 ≤ 1 := by nlinarith
  have hx0l : -x 0 ≤ 1 := by nlinarith
  have hx2u : x 2 ≤ 1 := by nlinarith
  have hx2l : -x 2 ≤ 1 := by nlinarith
  have hx3u : x 3 ≤ 1 := by nlinarith
  have hx3l : -x 3 ≤ 1 := by nlinarith
  have hx1u : x 1 ≤ 1 := by nlinarith
  have hx1l : -x 1 ≤ 1 := by nlinarith
  fin_cases i
  · exact abs_le.2 ⟨neg_le.mp hx0l, hx0u⟩
  · exact abs_le.2 ⟨neg_le.mp hx1l, hx1u⟩
  · exact abs_le.2 ⟨neg_le.mp hx2l, hx2u⟩
  · exact abs_le.2 ⟨neg_le.mp hx3l, hx3u⟩
  · exact abs_le.2 ⟨neg_le.mp hx4l, hx4u⟩

lemma q28_bounded : Bornology.IsBounded (Hpoly q28A q28B) := by
  refine (isBounded_iff_forall_norm_le).2 ⟨Real.sqrt 5, ?_⟩
  intro x hx
  have hi : ∀ i : Fin 5, |x i| ≤ 1 := fun i => coord_abs_le_one hx i
  have hsq : ‖x‖ ^ 2 = ∑ i : Fin 5, |x i| ^ 2 := by
    simpa [sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin 5 => ℝ) x
  have : ‖x‖ ^ 2 ≤ 5 := by
    rw [hsq]
    have : ∀ i : Fin 5, |x i| ^ 2 ≤ 1 := fun i => by
      have h := hi i
      have : |x i| ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using h)
      simpa using this
    calc
      ∑ i : Fin 5, |x i| ^ 2 ≤ ∑ _i : Fin 5, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => this i
      _ = 5 := by simp
  have hnn : 0 ≤ (5 : ℝ) := by norm_num
  rw [← Real.sqrt_sq (norm_nonneg x)]
  exact Real.sqrt_le_sqrt this

lemma q28U_extreme : q28U ∈ extremePoints ℝ (Hpoly q28A q28B) := by
  refine ⟨q28U_mem, ?_⟩
  intro p hp q hq hop
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hop
  have tight (i : Fin 28) (htop : q28A i (4 : Fin 5) = 1) :
      ⟪q28A i, p⟫ = 1 ∧ ⟪q28A i, q⟫ = 1 := by
    have hU : ⟪q28A i, q28U⟫ = 1 := by simp [inner_q28U, htop]
    have hp' : ⟪q28A i, p⟫ ≤ 1 := by simpa [q28B] using hp i
    have hq' : ⟪q28A i, q⟫ ≤ 1 := by simpa [q28B] using hq i
    have : α * ⟪q28A i, p⟫ + β * ⟪q28A i, q⟫ = 1 := by
      have := congrArg (fun z => ⟪q28A i, z⟫) hcomb
      simp [inner_add_right, inner_smul_right, hU] at this
      exact this
    constructor <;> nlinarith
  have t0 := tight 0 (by simp [q28A_0, vec5_last])
  have t1 := tight 1 (by simp [q28A_1, vec5_last])
  have t2 := tight 2 (by simp [q28A_2, vec5_last])
  have t4 := tight 4 (by simp [q28A_4, vec5_last])
  have t6 := tight 6 (by simp [q28A_6, vec5_last])
  have hp0 : 18 * p 0 + p (4 : Fin 5) = 1 := by simpa [q28A_0, inner_vec5] using t0.1
  have hp1 : -18 * p 0 + p (4 : Fin 5) = 1 := by simpa [q28A_1, inner_vec5] using t1.1
  have hp2 : 30 * p 2 + p (4 : Fin 5) = 1 := by simpa [q28A_2, inner_vec5] using t2.1
  have hp4 : 30 * p 3 + p (4 : Fin 5) = 1 := by simpa [q28A_4, inner_vec5] using t4.1
  have hp6 : 5 * p 1 + 25 * p 3 + p (4 : Fin 5) = 1 := by simpa [q28A_6, inner_vec5] using t6.1
  have hp4c : p (4 : Fin 5) = 1 := by linarith
  have hp0c : p 0 = 0 := by linarith
  have hp2c : p 2 = 0 := by linarith
  have hp3c : p 3 = 0 := by linarith
  have hp1c : p 1 = 0 := by linarith
  have : p = q28U := by
    ext i
    fin_cases i
    · simpa [q28U, PiLp.single_eq_of_ne (p := 2) (by decide : (0 : Fin 5) ≠ 4)] using hp0c
    · simpa [q28U, PiLp.single_eq_of_ne (p := 2) (by decide : (1 : Fin 5) ≠ 4)] using hp1c
    · simpa [q28U, PiLp.single_eq_of_ne (p := 2) (by decide : (2 : Fin 5) ≠ 4)] using hp2c
    · simpa [q28U, PiLp.single_eq_of_ne (p := 2) (by decide : (3 : Fin 5) ≠ 4)] using hp3c
    · simpa [q28U, PiLp.single_eq_same] using hp4c
  exact this

lemma q28V_extreme : q28V ∈ extremePoints ℝ (Hpoly q28A q28B) := by
  refine ⟨q28V_mem, ?_⟩
  intro p hp q hq hop
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hop
  have tight (i : Fin 28) (hbot : q28A i (4 : Fin 5) = -1) :
      ⟪q28A i, p⟫ = 1 ∧ ⟪q28A i, q⟫ = 1 := by
    have hV : ⟪q28A i, q28V⟫ = 1 := by simp [inner_q28V, hbot]
    have hp' : ⟪q28A i, p⟫ ≤ 1 := by simpa [q28B] using hp i
    have hq' : ⟪q28A i, q⟫ ≤ 1 := by simpa [q28B] using hq i
    have : α * ⟪q28A i, p⟫ + β * ⟪q28A i, q⟫ = 1 := by
      have := congrArg (fun z => ⟪q28A i, z⟫) hcomb
      simp [inner_add_right, inner_smul_right, hV] at this
      exact this
    constructor <;> nlinarith
  have t16 := tight 16 (by simp [q28A_16, vec5_last])
  have t17 := tight 17 (by simp [q28A_17, vec5_last])
  have t18 := tight 18 (by simp [q28A_18, vec5_last])
  have t19 := tight 19 (by simp [q28A_19, vec5_last])
  have t14 : q28A 14 = vec5 0 0 18 0 (-1) := rfl
  have t14' := tight 14 (by simp [t14, vec5_last])
  have hp16 : 30 * p 1 - p (4 : Fin 5) = 1 := by simpa [q28A_16, inner_vec5] using t16.1
  have hp17 : -30 * p 1 - p (4 : Fin 5) = 1 := by simpa [q28A_17, inner_vec5] using t17.1
  have hp18 : 30 * p 0 - p (4 : Fin 5) = 1 := by simpa [q28A_18, inner_vec5] using t18.1
  have hp19 : -30 * p 0 - p (4 : Fin 5) = 1 := by simpa [q28A_19, inner_vec5] using t19.1
  have hp14 : 18 * p 2 - p (4 : Fin 5) = 1 := by simpa [t14, inner_vec5] using t14'.1
  have hp4c : p (4 : Fin 5) = -1 := by linarith
  have hp1c : p 1 = 0 := by linarith
  have hp0c : p 0 = 0 := by linarith
  have hp2c : p 2 = 0 := by linarith
  have t20 : q28A 20 = vec5 25 0 0 5 (-1) := rfl
  have t20' := tight 20 (by simp [t20, vec5_last])
  have hp20 : 25 * p 0 + 5 * p 3 - p (4 : Fin 5) = 1 := by simpa [t20, inner_vec5] using t20'.1
  have hp3c : p 3 = 0 := by linarith
  have : p = q28V := by
    ext i
    fin_cases i
    · simpa [q28V, PiLp.single_eq_of_ne (p := 2) (by decide : (0 : Fin 5) ≠ 4)] using hp0c
    · simpa [q28V, PiLp.single_eq_of_ne (p := 2) (by decide : (1 : Fin 5) ≠ 4)] using hp1c
    · simpa [q28V, PiLp.single_eq_of_ne (p := 2) (by decide : (2 : Fin 5) ≠ 4)] using hp2c
    · simpa [q28V, PiLp.single_eq_of_ne (p := 2) (by decide : (3 : Fin 5) ≠ 4)] using hp3c
    · simpa [q28V, PiLp.single_eq_same] using hp4c
  exact this

lemma q28_zero_mem : (0 : EuclideanSpace ℝ (Fin 5)) ∈ Hpoly q28A q28B := by
  intro i
  simp [q28B, inner_zero_right]

theorem solution :
    ∃ (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 5)) (b : Fin n → ℝ)
      (u v : EuclideanSpace ℝ (Fin 5)),
      25 ≤ n ∧
      (Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hpoly a b) ∧
      u ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      (∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
        ¬ (w 0 = u ∧ w 5 = v ∧
            ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) := by
  refine ⟨28, q28A, q28B, q28U, q28V, ?_, ?_, q28_bounded, q28U_extreme, q28V_extreme,
    q28_xor, q28_polar_no_length_five_walk⟩
  · decide
  · exact ⟨0, q28_zero_mem⟩
