-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_bounded_drop_mass_pos
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:13:37.945991+00:00
-- url     : https://prove2.me/submissions/f0862a90-26e7-4901-92da-53db4f4a2b37

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma kernelMass_nonneg (n : ℕ) : 0 ≤ kernelMass n :=
  Finset.sum_nonneg (fun _ hm => erdosWeight_nonneg_of_mem hm)

lemma Pker_nonneg (n k : ℕ) : 0 ≤ Pker n k := by
  unfold Pker
  split_ifs with h
  · exact div_nonneg (erdosWeight_nonneg_of_lt (by omega)) (kernelMass_nonneg n)
  · exact le_refl 0

/-- Reflection `k ↦ n−k` on `Icc 1 (n−1)`. -/
lemma sum_Icc_reflect_sub (n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (n - 1), F (n - k) = ∑ m ∈ Finset.Icc 1 (n - 1), F m := by
  apply Finset.sum_nbij' (fun k => n - k) (fun m => n - m)
  · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro k hk; rw [Finset.mem_Icc] at hk; omega
  · intro m hm; rw [Finset.mem_Icc] at hm; omega
  · intro k _; rfl

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- A `√`-gap exceeding `1/3` forces a strict rank drop (since `rnk = ⌊3√·⌋`). -/
lemma rnk_lt_of_sqrt_gap {n k : ℕ} (h : (1:ℝ)/3 < Real.sqrt n - Real.sqrt k) :
    rnk k < rnk n := by
  unfold rnk
  rw [← Nat.add_one_le_iff]
  apply Nat.le_floor
  push_cast
  have hfk : (⌊3 * Real.sqrt k⌋₊ : ℝ) ≤ 3 * Real.sqrt k := Nat.floor_le (by positivity)
  linarith

/-- **Window steps drop rank.** If `√n < m` (the window lower edge `a₀=1`) then the predecessor
`n − m` has strictly smaller rank: `√n − √(n−m) > 1/2 > 1/3`. -/
lemma window_rank_drop {n m : ℕ} (hn : 1 ≤ n) (hmn : m < n)
    (hmlb : Real.sqrt (n : ℝ) < (m : ℝ)) :
    rnk (n - m) < rnk n := by
  apply rnk_lt_of_sqrt_gap
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hble : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (le_of_lt hmn)]
  have hprod : (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
      * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) = (m : ℝ) := by
    have e1 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    have e2 : Real.sqrt ((n - m : ℕ) : ℝ) ^ 2 = (n : ℝ) - m := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  have hsumpos : 0 < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by linarith [Real.sqrt_nonneg ((n - m : ℕ) : ℝ)]
  have hgap : Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)
      = (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hsumpos)]; exact hprod
  rw [hgap, lt_div_iff₀ hsumpos]
  nlinarith [hmlb, hble, ha]

/-- The fixed window `(√n, 2√n]` carries a uniform positive kernel mass (the `a₀=1` instance of
`erdos_kernel_fixed_window_pos`, exposed explicitly so window steps `m>√n` apply `window_rank_drop`). -/
lemma kernelWindow_one_two_pos :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᶠ n : ℕ in atTop, ν ≤ kernelWindow 1 2 n := by
  have hC := C_pos
  have hIpos : 0 < Model.modelIntegral C 1 2 := by
    rw [Model.modelIntegral]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
        have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
          continuous_const.mul continuous_id
        have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact h1.mul h2
      exact hc.intervalIntegrable _ _
    · intro y hy
      have hy1 : (1 : ℝ) < y := hy.1
      have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
      have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
      nlinarith [mul_pos (mul_pos hπ (by linarith : (0:ℝ) < y)) he]
    · norm_num
  refine ⟨Model.modelIntegral C 1 2 / 2, by positivity, ?_⟩
  have hwin := Model.erdos_kernel_window (a := 1) (b := 2) zero_le_one one_lt_two
  have hev := (tendsto_order.1 hwin).1 (Model.modelIntegral C 1 2 / 2) (by linarith)
  filter_upwards [hev] with n hn
  exact hn.le

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# TASK 11, Step E (partial): the local bounded-rank-drop lower bound

The honest local kernel content available from the banked window mass: from a state `n`, a uniformly
positive `Pker`-mass (`≥ ν/2`) lands at a predecessor whose rank drops by a **bounded** amount
(at most `7`) — the window steps `m ∈ (√n, 2√n]` drop rank by `rnk n − rnk(n−m) ∈ [1, 7]`.  This is the
local-limit lower bound the entrance-overlap analysis needs *at the ceiling* (a state sitting just
above a band lands inside it with positive mass).

This does **not** by itself give the first-entrance *overlap between two different starts*, nor does it
kill the overshoot escape at fixed band width — those are the renewal-overshoot equidistribution
content.  It is the strongest fragment of Step E derivable from
the banked window mass, and is reusable for any renewal-coupling attempt.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- A window step `m ∈ (√n, 2√n]` drops rank by at most `7`: `rnk n − rnk (n−m) ≤ 7`, equivalently
`rnk n ≤ rnk (n−m) + 7`. -/
lemma window_rank_drop_bounded {n m : ℕ} (hn : 1 ≤ n) (hmn : m < n)
    (hmub : (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)) :
    rnk n ≤ rnk (n - m) + 7 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- √n − √(n−m) = m/(√n+√(n−m)) ≤ 2√n/√n = 2
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (le_of_lt hmn)]
  have hsa : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsble : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hsbnn : 0 ≤ Real.sqrt ((n - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  -- (√n − √(n−m))·(√n + √(n−m)) = m
  have hprod : (Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ))
      * (Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ)) = (m:ℝ) := by
    have e1 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
    have e2 : Real.sqrt ((n-m:ℕ):ℝ) ^ 2 = (n:ℝ) - m := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  have hsumpos : 0 < Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ) := by linarith
  have hgap_le : Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ) ≤ 2 := by
    -- (√n − √(n−m)) = m / (√n+√(n−m)) ≤ 2√n / √n = 2
    have hgap_eq : Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ)
        = (m:ℝ) / (Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ)) := by
      rw [eq_div_iff (ne_of_gt hsumpos)]; exact hprod
    rw [hgap_eq, div_le_iff₀ hsumpos]
    nlinarith [hmub, hsble, hsbnn, hsa]
  -- rnk n = ⌊3√n⌋ ≤ 3√n < 3√(n−m) + 6 + 1 ≤ (rnk(n−m)+1) + 6 + ... carefully via floors
  have hfn : (rnk n : ℝ) ≤ 3 * Real.sqrt (n:ℝ) := (rnk_sqrt_bounds n).1
  have hfnm : 3 * Real.sqrt ((n-m:ℕ):ℝ) < (rnk (n-m) : ℝ) + 1 := (rnk_sqrt_bounds (n-m)).2
  -- 3√n ≤ 3√(n−m) + 6  (since √n − √(n−m) ≤ 2)
  have h3 : 3 * Real.sqrt (n:ℝ) ≤ 3 * Real.sqrt ((n-m:ℕ):ℝ) + 6 := by nlinarith [hgap_le]
  have hlt : (rnk n : ℝ) < (rnk (n-m) : ℝ) + 7 := by linarith
  have hnat : (rnk n : ℝ) < ((rnk (n-m) + 7 : ℕ) : ℝ) := by push_cast; linarith
  have : rnk n < rnk (n-m) + 7 := by exact_mod_cast hnat
  omega

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
theorem solution :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      μ ≤ ∑ k ∈ (Finset.range n).filter
            (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k := by
  obtain ⟨ν, hνpos, hνmass⟩ := kernelWindow_one_two_pos
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hone : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  refine ⟨ν / 2, by positivity, ?_⟩
  filter_upwards [hνmass, hKev, hone, Filter.eventually_ge_atTop 2] with n hνn hKn hKn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKn
  have hS2 : kernelMass n ≤ 2 := by linarith [hSup, hKn1]
  have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hSlo, hKn1]
  have hSpos : (0 : ℝ) < kernelMass n := by linarith
  have hkey : kernelWindow 1 2 n / kernelMass n
      ≤ ∑ k ∈ (Finset.range n).filter
          (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k := by
    have hreflect : kernelWindow 1 2 n / kernelMass n
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            (if 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
                ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
              then Pker n k else 0) := by
      rw [kernelWindow, ← sum_Icc_reflect_sub n
        (fun m => if 1 * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
          then erdosWeight n m else 0), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hw : 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
          ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
      · rw [if_pos hw, if_pos hw]
        unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
      · rw [if_neg hw, if_neg hw, zero_div]
    rw [hreflect, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
      rw [Finset.mem_filter, Finset.mem_range]
      have hmlt : n - k < n := by omega
      have hsubeq : n - (n - k) = k := Nat.sub_sub_self (by omega : k ≤ n)
      -- strict drop
      have hdrop := window_rank_drop (n := n) (m := n - k) (by omega) hmlt (by
        rw [one_mul] at hw1; exact hw1)
      rw [hsubeq] at hdrop
      -- bounded drop ≤ 7
      have hbnd := window_rank_drop_bounded (n := n) (m := n - k) (by omega) hmlt (by
        exact hw2)
      rw [hsubeq] at hbnd
      exact ⟨by omega, hbnd, hdrop⟩
    · intro k _ _; exact Pker_nonneg n k
  refine le_trans ?_ hkey
  rw [le_div_iff₀ hSpos]
  nlinarith [hνn, hS2, hνpos]
