-- Prove2me | solution 1 for mme_prescribed_cell_parent_profile_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:20:33.125452+00:00
-- url     : https://prove2.me/submissions/478a0ddd-63c4-4fcf-95e2-956115eaa193

import Theorems.Thm_mme_prescribed_cell_pair_pattern_concentration
import Theorems.Thm_mme_prescribed_cell_histogram_nonempty

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem event_union {U J : Type*} [Fintype U] [Nonempty U] [Fintype J]
    (bad : J → U → Prop) (B : ℝ)
    (hb : ∀ j, (𝔼 f : U, if bad j f then (1 : ℝ) else 0) ≤ B) :
    (𝔼 f : U, if ∃ j, bad j f then (1 : ℝ) else 0) ≤ Fintype.card J * B := by
  classical
  calc
    _ ≤ 𝔼 f : U, (∑ j : J, if bad j f then (1 : ℝ) else 0) := by
      apply Finset.expect_le_expect
      intro f _
      by_cases h : ∃ j, bad j f
      · obtain ⟨j,hj⟩ := h
        have ht := Finset.single_le_sum (f := fun j : J ↦ if bad j f then (1 : ℝ) else 0)
          (fun k _ ↦ by dsimp; split_ifs <;> norm_num) (Finset.mem_univ j)
        rw [if_pos ⟨j,hj⟩]
        simpa only [if_pos hj] using ht
      · simp [h]
    _ = ∑ j : J, (𝔼 f : U, if bad j f then (1 : ℝ) else 0) := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : J, B := Finset.sum_le_sum (fun j _ ↦ hb j)
    _ = _ := by simp

theorem solution {P C W R : Type*} [Fintype P] [Fintype C] [Fintype W] [Fintype R]
    (cell : P → C) (mu : C → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c})
    (n : R → ℕ) (q : (r : R) → Fin (n r) × Fin 2 → P)
    (hq : ∀ r, Function.Injective (q r))
    (center : R → (Fin 2 → W) → ℝ)
    (hcenter : ∀ r w, center r w =
      (∑ t : Fin (n r), ∏ h : Fin 2, ((mu (cell (q r (t,h))) (w h) : ℝ) /
        Fintype.card {p : P // cell p = cell (q r (t,h))})) / n r)
    (m : ℕ) (hm : 0 < m) (hmn : ∀ r, m ≤ n r)
    (hsize : ∀ r t h, m ≤ Fintype.card {p : P // cell p = cell (q r (t,h))})
    (eps : ℝ) (heps : 0 < eps) :
    (𝔼 f : {f : P → W // Useful cell mu f},
      if ∃ r w, eps ≤ |(Fintype.card {t : Fin (n r) // ∀ h, f.val (q r (t,h)) = w h} : ℝ) /
          n r - center r w| then (1 : ℝ) else 0) ≤
      25 * Fintype.card R * (Fintype.card W : ℝ) ^ 2 / ((m : ℝ) * eps ^ 2) := by
  classical
  let U := {f : P → W // Useful cell mu f}
  have hU := mme_prescribed_cell_histogram_nonempty cell mu hmass
  letI : Nonempty U := hU
  let bad (j : R × (Fin 2 → W)) (f : U) :=
    eps ≤ |(Fintype.card {t : Fin (n j.1) // ∀ h, f.val (q j.1 (t,h)) = j.2 h} : ℝ) /
      n j.1 - center j.1 j.2|
  have hb (j : R × (Fin 2 → W)) : (𝔼 f : U, if bad j f then (1 : ℝ) else 0) ≤
      25 / ((m : ℝ) * eps ^ 2) := by
    have h := mme_prescribed_cell_pair_pattern_concentration cell mu (q j.1) (hq j.1) j.2 hU
      m hm (by simpa using hmn j.1) (hsize j.1) eps heps
    have heq (f : {f : P → W // Useful cell mu f}) : ((∑ t : Fin (n j.1), if (∀ h : Fin 2, f.val (q j.1 (t,h)) = j.2 h) then (1 : ℝ) else 0) -
        ∑ t : Fin (n j.1), ∏ h : Fin 2, ((mu (cell (q j.1 (t,h))) (j.2 h) : ℝ) /
          Fintype.card {p : P // cell p = cell (q j.1 (t,h))})) / Fintype.card (Fin (n j.1)) =
        (Fintype.card {t : Fin (n j.1) // ∀ h, f.val (q j.1 (t,h)) = j.2 h} : ℝ) /
          n j.1 - center j.1 j.2 := by
      rw [hcenter, Fintype.card_fin, sub_div]
      congr 2
      simp only [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simpa only [heq, bad] using h
  have h := event_union bad (25 / ((m : ℝ) * eps ^ 2)) hb
  have hex (f : U) : (∃ j, bad j f) ↔
      ∃ r w, eps ≤ |(Fintype.card {t : Fin (n r) // ∀ h, f.val (q r (t,h)) = w h} : ℝ) /
          n r - center r w| := by simp only [bad, Prod.exists]
  simp only [hex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow] at h
  convert h using 1 <;> ring
