-- Prove2me | solution 1 for Zeta23.MV.Adm.integral_inv_sq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:36:23.276909+00:00
-- url     : https://prove2.me/submissions/920b8bdc-6021-411f-8883-d318a74b2269

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

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

theorem solution {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 2)⁻¹ = (a - c)⁻¹ - (b - c)⁻¹ := by
  have h0 : (0:ℝ) ∉ Set.uIcc (a - c) (b - c) := by
    rw [Set.mem_uIcc]
    rcases hc with hc | hc
    · push Not; constructor <;> intro <;> nlinarith
    · push Not; constructor <;> intro <;> nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e1 : ∀ u : ℝ, ((u - c) ^ 2)⁻¹ = (u - c) ^ (-2 : ℤ) := by
    intro u; rw [zpow_neg]; norm_cast
  simp_rw [e1]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-2:ℤ)) c,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num [zpow_neg]
  ring
