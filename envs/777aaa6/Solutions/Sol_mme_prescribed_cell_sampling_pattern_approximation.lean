-- Prove2me | solution 1 for mme_prescribed_cell_sampling_pattern_approximation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:54:03.965294+00:00
-- url     : https://prove2.me/submissions/e9f2b5a8-e490-49f4-bff6-7591e747fe09

import Theorems.Thm_mme_prescribed_cell_sampling_moment_count
import Theorems.Thm_mme_prescribed_cell_sampling_collision_bound
import Mathlib.Algebra.BigOperators.Expect

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {P C W J : Type*} [Fintype P] [Fintype W] [Fintype J]
    (cell : P → C) (mu : C → W → ℕ) (q : J → P) (hq : Function.Injective q) (w : J → W)
    (hU : Nonempty {f : P → W // Useful cell mu f}) (m : ℕ) (hm : 0 < m)
    (hsize : ∀ j, m ≤ Fintype.card {p : P // cell p = cell (q j)}) :
    |(𝔼 f : {f : P → W // Useful cell mu f}, if (∀ j, f.val (q j) = w j) then (1 : ℝ) else 0) -
      ∏ j, ((mu (cell (q j)) (w j) : ℝ) / Fintype.card {p : P // cell p = cell (q j)})| ≤
        (Fintype.card J : ℝ) ^ 2 / m := by
  classical
  let U := {f : P → W // Useful cell mu f}
  let Samples := (j : J) → {p : P // cell p = cell (q j)}
  letI : Nonempty U := hU
  letI : Nonempty Samples := ⟨fun j ↦ ⟨q j,rfl⟩⟩
  let A := Fintype.card {f : U // ∀ j, f.val (q j) = w j}
  let B := Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)}
  let R := ∏ j, (mu (cell (q j)) (w j) : ℝ)
  have hcount : |(Fintype.card Samples : ℝ) * A - (Fintype.card U : ℝ) * R| ≤
      (Fintype.card U : ℝ) * B := mme_prescribed_cell_sampling_moment_count cell mu q hq w
  have hb : (m : ℝ) * B ≤ (Fintype.card J : ℝ) ^ 2 * Fintype.card Samples := by
    exact_mod_cast mme_prescribed_cell_sampling_collision_bound cell q m hsize
  have hs : (0 : ℝ) < Fintype.card Samples := by exact_mod_cast Fintype.card_pos
  have hu : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmean : (𝔼 f : U, if (∀ j, f.val (q j) = w j) then (1 : ℝ) else 0) =
      (A : ℝ) / Fintype.card U := by
    rw [Fintype.expect_eq_sum_div_card]
    congr 1
    change (∑ f : U, if (∀ j, f.val (q j) = w j) then (1 : ℝ) else 0) = (A : ℝ)
    simp only [A, U, Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hprod : (∏ j, ((mu (cell (q j)) (w j) : ℝ) /
      Fintype.card {p : P // cell p = cell (q j)})) = R / Fintype.card Samples := by
    rw [Finset.prod_div_distrib]
    congr 1
    simp only [Samples, Fintype.card_pi, Nat.cast_prod]
  change |(𝔼 f : U, if (∀ j, f.val (q j) = w j) then (1 : ℝ) else 0) - _| ≤ _
  rw [hmean, hprod]
  have hid : (Fintype.card Samples : ℝ) * Fintype.card U *
      |(A : ℝ) / Fintype.card U - R / Fintype.card Samples| =
      |(Fintype.card Samples : ℝ) * A - (Fintype.card U : ℝ) * R| := by
    rw [← abs_of_pos (mul_pos hs hu), ← abs_mul]
    congr 1
    field_simp
  have h1 := mul_le_mul_of_nonneg_left hcount hm'.le
  have h2 := mul_le_mul_of_nonneg_left hb hu.le
  rw [← hid] at h1
  apply (le_div_iff₀ hm').mpr
  have hmul : (Fintype.card Samples : ℝ) * Fintype.card U *
      (|(A : ℝ) / Fintype.card U - R / Fintype.card Samples| * m) ≤
      (Fintype.card Samples : ℝ) * Fintype.card U * (Fintype.card J : ℝ) ^ 2 := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (mul_pos hs hu)).mp hmul
