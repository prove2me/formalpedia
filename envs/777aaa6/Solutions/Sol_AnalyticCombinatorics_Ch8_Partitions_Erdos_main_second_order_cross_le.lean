-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.main_second_order_cross_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:49.537341+00:00
-- url     : https://prove2.me/submissions/22f49b03-c9a5-4998-8f9b-233de519be41

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_kernel_error_rhoModel_le
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Mass-rate campaign: second-order kernel expansions (R8 §3.2–3.3)

Second-order expansions of the square-root drop and the reciprocal, with explicit
error constants:

* `sqrt_drop_second_order` — `|（√n−√(n−m)) − (m/(2s) + m²/(8s³))| ≤ m³/s⁵` for `m ≤ n`,
  via the purely algebraic identity `8s³E = (s−q)³(q+3s)` (`s=√n`, `q=√(n−m)`,
  `linear_combination` on `q² = s²−m`) — no calculus, no smallness hypothesis;
* `inv_sub_second_order` — `|1/(n−m) − (1/n + m/n²)| = m²/(n²(n−m)) ≤ 2m²/n³` for `2m ≤ n`.

Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Square-root drop, second order**: for `m ≤ n`, `1 ≤ n`,

  `|（√n − √(n−m)) − (m/(2√n) + m²/(8√n³))| ≤ m³/√n⁵`.
-/
lemma sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- the key polynomial identity: 8s⁴ − 8s³q − 4s²m − m² = (s−q)³(q+3s)
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  -- the expression E in closed form
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  -- nonnegativity and the bound
  have hsq_nonneg : 0 ≤ s - q := by linarith
  have hE_nonneg : 0 ≤ (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    have h1 : 0 ≤ (s - q) ^ 3 := by positivity
    have h2 : 0 ≤ q + 3 * s := by linarith
    positivity
  rw [hE_eq, abs_of_nonneg hE_nonneg]
  -- (s−q)(s+q) = m so s−q ≤ m/s; q+3s ≤ 4s
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [this, hq2]
    ring
  have hsq_le : s - q ≤ (m : ℝ) / s := by
    rw [le_div_iff₀ hs]
    calc (s - q) * s ≤ (s - q) * (s + q) :=
          mul_le_mul_of_nonneg_left (by linarith) hsq_nonneg
      _ = (m : ℝ) := hprod
  have hq3s : q + 3 * s ≤ 4 * s := by linarith
  calc (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3)
      ≤ ((m : ℝ) / s) ^ 3 * (4 * s) / (8 * s ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul _ hq3s (by linarith) (by positivity)
        exact pow_le_pow_left₀ hsq_nonneg hsq_le 3
    _ = (m : ℝ) ^ 3 / (2 * s ^ 5) := by
        field_simp
        ring
    _ ≤ (m : ℝ) ^ 3 / s ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hs 5]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Numerator model: the second-order `ρ`-drop and its error

The drift numerator is `muNum n = ∑_m erdosWeight n m · rhoDrop n m` with
`rhoDrop n m = 3(√n − √(n−m))`.  Its model replaces the `√`-drop by its two-term Taylor
expansion (`sqrt_drop_second_order`):

  `rhoDropModel n m = 3( m/(2√n) + m²/(8(√n)³) )`,   `|rhoDrop − rhoDropModel| ≤ 3 m³/(√n)⁵`.

This is the `ρ`-drop half of the `muNum` expansion (the kernel half is the banked `modelSummand`).
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **ρ-drop model error**: `|rhoDrop n m − rhoDropModel n m| ≤ 3 m³/(√n)⁵`. -/
lemma rhoDrop_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |rhoDrop n m - rhoDropModel n m| ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hkey := sqrt_drop_second_order hn hm
  have heq : rhoDrop n m - rhoDropModel n m
      = 3 * ((Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
          - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
            + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))) := by
    rw [rhoDrop, rhoDropModel]; ring
  rw [heq, abs_mul, show |(3 : ℝ)| = 3 from by norm_num]
  have : 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 = 3 * ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5) := by
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hkey (by norm_num)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

private lemma rhoDropModel_nonneg (n m : ℕ) :
    0 ≤ rhoDropModel n m := by
  rw [rhoDropModel]
  positivity

private lemma main_cut_two_mul_le {n m : ℕ} (hn8 : 8 ≤ n)
    (hmle : m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊) :
    2 * m ≤ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hp23 : (0 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hnpos.le _
  have hmr : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
    le_trans (by exact_mod_cast hmle) (Nat.floor_le hp23)
  have hcubrt : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have hmono : (8 : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
    have h83 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h83] at hmono
  have hn_factor : (n : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hnpos, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
  have hreal : 2 * (m : ℝ) ≤ (n : ℝ) := by
    calc
      2 * (m : ℝ) ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) := by linarith
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcubrt hp23
      _ = (n : ℝ) := hn_factor.symm
  exact_mod_cast hreal

private lemma rhoDrop_sub_model_le_model_of_main
    {n m : ℕ} (hn8 : 8 ≤ n) (hm1 : 1 ≤ m)
    (hmle : m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊) :
    |rhoDrop n m - rhoDropModel n m| ≤ |rhoDropModel n m| := by
  have hn1 : 1 ≤ n := by omega
  have h2m : 2 * m ≤ n := main_cut_two_mul_le hn8 hmle
  have hmn : m ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs4 : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    rw [show Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 by ring, hs2]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm1
  have h2mR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m
  have h2m2 : 2 * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [h2mR, sq_nonneg ((n : ℝ) - 2 * (m : ℝ)),
      sq_nonneg (m : ℝ)]
  have hcore : (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5
      ≤ (m : ℝ) / (2 * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ (pow_pos hs0 5) (mul_pos (by norm_num) hs0)]
    rw [show (m : ℝ) ^ 3 * (2 * Real.sqrt (n : ℝ))
        = (2 * (m : ℝ) ^ 2) * ((m : ℝ) * Real.sqrt (n : ℝ)) by ring]
    rw [show (m : ℝ) * Real.sqrt (n : ℝ) ^ 5
        = (Real.sqrt (n : ℝ) ^ 4) * ((m : ℝ) * Real.sqrt (n : ℝ)) by ring]
    rw [hs4]
    exact mul_le_mul_of_nonneg_right h2m2 (mul_nonneg hmpos.le hs0.le)
  calc
    |rhoDrop n m - rhoDropModel n m|
        ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := rhoDrop_sub_model_le hn1 hmn
    _ = 3 * ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5) := by ring
    _ ≤ 3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 3)
    _ ≤ rhoDropModel n m := by
        rw [rhoDropModel]
        have hrest : 0 ≤ (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3) := by positivity
        nlinarith
    _ = |rhoDropModel n m| := (abs_of_nonneg (rhoDropModel_nonneg n m)).symm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := main_kernel_error_rhoModel_le
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop 8] with n hKn hn8
  calc
    (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDropModel n m| := by
          refine Finset.sum_le_sum ?_
          intro m hm
          rw [Finset.mem_Icc] at hm
          exact mul_le_mul_of_nonneg_left
            (rhoDrop_sub_model_le_model_of_main hn8 hm.1 hm.2)
            (abs_nonneg _)
    _ ≤ K / (n : ℝ) := hKn
