-- Prove2me | solution 1 for Zeta23.MV.eigen_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:23:45.137492+00:00
-- url     : https://prove2.me/submissions/50cc4f70-d2b2-448c-bb2d-f4a58edfd882

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Zeta23_MV_Quadratic
import Definitions.Def_Zeta23_MV_Spacing
import Theorems.Thm_Zeta23_MV_Adm_spacing_sq
import Theorems.Thm_Zeta23_MV_Uform_le
import Theorems.Thm_Zeta23_MV_eigen_identityPrime

-- from Zeta23.MV.Quadratic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 1 — the quadratic-form bound `U ≤ 73 V` (arXiv:2203.14950 Thm 1.2 shape)

`U := Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²  ≤  73 Σ t_n² ` for nonneg `t`:
Cauchy–Schwarz `U² ≤ V·W`; `W = S + T` (diagonal/off-diagonal of the expanded square);
`S ≤ 27V` (σ=4 spacing); `T ≤ 72U` (two-point lemma); the quadratic inequality gives `U ≤ 73V`.
-/

noncomputable section
open Real Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}


/-- Swap the two layers of an `erase`-nested double sum. -/
lemma sum_erase_comm {M : Type*} [AddCommMonoid M] (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩



end MV
end Zeta23
end
end

-- from Zeta23.MV.Eigen
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV steps 2–3 — the Preissmann–Lévêque eigen-identity and the eigenvalue bound

* `eigen_identity` (arXiv:2203.14950 Lemma 2.1): pure Finset algebra
  over ℂ + partial fractions + the conjugate eigen-relation; the `−iμ` cross piece dies under
  `Re` — the cancellation at the heart of Montgomery–Vaughan.
* `eigen_bound`: with `c = √δ`, summing the identity over `m` for a unit
  eigenvector and inserting `spacing_sq` (≤ 9) and `Uform_le` (≤ 73):
  `μ² ≤ 9 + 2·73 = 155 ≤ 13²`.
-/

noncomputable section
open Real Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}



end MV
end Zeta23
end
open Real Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

theorem solution (h : Adm freq δ) (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 13 := by
  classical
  set c : ι → ℝ := fun r => Real.sqrt (δ r) with hc
  have hcpos : ∀ r, 0 < c r := fun r => Real.sqrt_pos.2 (h.pos r)
  have hid := eigen_identityPrime h.inj c hcpos u μ heig
  have hsumid : μ ^ 2
      = (∑ m, ∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
        + 2 * ∑ m, ∑ n ∈ Finset.univ.erase m,
            c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2 := by
    calc μ ^ 2 = μ ^ 2 * ∑ m, ‖u m‖ ^ 2 := by rw [hu, mul_one]
      _ = ∑ m, μ ^ 2 * ‖u m‖ ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ m, ((∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
            + 2 * ∑ n ∈ Finset.univ.erase m,
                c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2) :=
          Finset.sum_congr rfl fun m _ => hid m
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS : (∑ m, ∑ n ∈ Finset.univ.erase m,
      (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2) ≤ 9 := by
    have e1 : ∀ m n, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2
        = (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) := by
      intro m n
      rw [hc]
      simp only [mul_pow, Real.sq_sqrt (h.pos m).le, Real.sq_sqrt (h.pos n).le,
        show (freq m - freq n) ^ 2 = (freq n - freq m) ^ 2 by ring]
      ring
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2
        = ∑ m, ∑ n ∈ Finset.univ.erase m, (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) :=
          Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => e1 m n
      _ = ∑ n, ∑ m ∈ Finset.univ.erase n, (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) :=
          sum_erase_comm _
      _ = ∑ n, (δ n * ‖u n‖ ^ 2) * ∑ m ∈ Finset.univ.erase n, δ m / (freq n - freq m) ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ n, (δ n * ‖u n‖ ^ 2) * (9 / δ n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          refine mul_le_mul_of_nonneg_left (h.spacing_sq n) ?_
          have := (h.pos n).le
          positivity
      _ = ∑ n, 9 * ‖u n‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          have hδn := (h.pos n).ne'
          field_simp
      _ = 9 := by rw [← Finset.mul_sum, hu, mul_one]
  have hT : |∑ m, ∑ n ∈ Finset.univ.erase m,
      c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| ≤ 73 := by
    have hper : ∀ m n : ι, |c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re
          / (freq m - freq n) ^ 2|
        ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 := by
      intro m n
      have hre : |(u m * (starRingEnd ℂ) (u n)).re| ≤ ‖u m‖ * ‖u n‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, RCLike.norm_conj]
      have hcube : c m ^ 3 = δ m * Real.sqrt (δ m) := by
        rw [hc]
        calc Real.sqrt (δ m) ^ 3 = Real.sqrt (δ m) ^ 2 * Real.sqrt (δ m) := by ring
          _ = δ m * Real.sqrt (δ m) := by rw [Real.sq_sqrt (h.pos m).le]
      rw [abs_div, abs_of_nonneg (sq_nonneg (freq m - freq n)), abs_mul, hcube]
      have hnn : (0:ℝ) ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) := by
        have := (h.pos m).le
        have := (h.pos n).le
        positivity
      have h1 : |δ m * Real.sqrt (δ m) * (c n)| = δ m * Real.sqrt (δ m) * Real.sqrt (δ n) := by
        rw [hc, abs_of_nonneg hnn]
      rw [h1]
      calc δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * |(u m * (starRingEnd ℂ) (u n)).re|
            / (freq m - freq n) ^ 2
          ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * (‖u m‖ * ‖u n‖)
              / (freq m - freq n) ^ 2 := by gcongr
        _ = δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖
              / (freq m - freq n) ^ 2 := by ring
    calc |∑ m, ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2|
        ≤ ∑ m, |∑ n ∈ Finset.univ.erase m,
            c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m,
            |c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| :=
          Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m,
            δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hper m n
      _ = Uform freq δ (fun r => ‖u r‖) := rfl
      _ ≤ 73 * ∑ n, ‖u n‖ ^ 2 := Uform_le h _ fun r => norm_nonneg _
      _ = 73 := by rw [hu, mul_one]
  have hmain : μ ^ 2 ≤ 155 := by
    have h2 := abs_le.1 hT
    linarith [hS, h2.1, h2.2]
  nlinarith [abs_nonneg μ, sq_abs μ]
