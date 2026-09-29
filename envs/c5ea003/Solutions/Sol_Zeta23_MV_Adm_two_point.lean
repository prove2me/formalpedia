-- Prove2me | solution 1 for Zeta23.MV.Adm.two_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:30:47.388221+00:00
-- url     : https://prove2.me/submissions/78298a3e-0bd9-4953-98a4-7491a02da88f

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing
import Theorems.Thm_Zeta23_MV_Adm_spacing_sq

-- from Zeta23.MV.Spacing
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)








section MainSpacing
variable (h : Adm freq δ) (s : ι)





end MainSpacing





end Adm
end MV
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)

theorem solution (h : Adm freq δ) {l m : ι} (hlm : l ≠ m) :
    ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
  classical
  have hδl := h.pos l
  have hδm := h.pos m
  have hflm : (freq l - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hlm (h.inj hh)
  have hC : 0 < (freq l - freq m) ^ 2 := pow_two_pos_of_ne_zero hflm
  have esq : ∀ x y : ℝ, (x - y) ^ 2 = (y - x) ^ 2 := fun x y => by ring
  have hsplit : ∀ k ∈ (Finset.univ.erase l).erase m,
      δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
        ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
          + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
    intro k hk
    have hkm : k ≠ m := Finset.ne_of_mem_erase hk
    have hkl : k ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkl' : (freq k - freq l) ≠ 0 := sub_ne_zero.2 fun hh => hkl (h.inj hh)
    have hkm' : (freq k - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hkm (h.inj hh)
    have hA : 0 < (freq k - freq l) ^ 2 := pow_two_pos_of_ne_zero hkl'
    have hB : 0 < (freq k - freq m) ^ 2 := pow_two_pos_of_ne_zero hkm'
    have hδk := h.pos k
    have htri : |freq l - freq m| ≤ |freq k - freq l| + |freq k - freq m| := by
      calc |freq l - freq m| = |(freq l - freq k) + (freq k - freq m)| := by ring_nf
        _ ≤ |freq l - freq k| + |freq k - freq m| := abs_add_le _ _
        _ = |freq k - freq l| + |freq k - freq m| := by rw [abs_sub_comm (freq l) (freq k)]
    have habs : 0 ≤ |freq l - freq m| := abs_nonneg _
    rcases le_total (|freq l - freq m| / 2) (|freq k - freq m|) with hP | hP
    · -- k far from m: keep the l-factor, crush the m-factor
      have hBC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq m) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hP 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq m) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hB hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq l - freq k) ^ 2) * (1 / (freq k - freq m) ^ 2) := by
          rw [esq (freq k) (freq l), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
    · -- k far from l
      have hAC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq l) ^ 2 := by
        have h2 : |freq l - freq m| / 2 ≤ |freq k - freq l| := by linarith
        have := pow_le_pow_left₀ (by positivity) h2 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq l) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hA hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq m - freq k) ^ 2) * (1 / (freq k - freq l) ^ 2) := by
          rw [mul_comm ((freq k - freq l) ^ 2) ((freq k - freq m) ^ 2),
            esq (freq k) (freq m), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
  calc ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ ∑ k ∈ (Finset.univ.erase l).erase m,
          (δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
            + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)) :=
        Finset.sum_le_sum hsplit
    _ = (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2)
        + (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ (9 / δ l) * (4 / (freq l - freq m) ^ 2) + (9 / δ m) * (4 / (freq l - freq m) ^ 2) := by
        have hsl : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2
            ≤ 9 / δ l := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_of_mem_erase hk) ?_) (h.spacing_sq l)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        have hsm : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2
            ≤ 9 / δ m := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ k⟩) ?_)
            (h.spacing_sq m)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        gcongr
    _ = 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
        field_simp
        ring
