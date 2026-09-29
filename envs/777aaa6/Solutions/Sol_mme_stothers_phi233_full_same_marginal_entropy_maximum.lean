-- Prove2me | solution 1 for mme_stothers_phi233_full_same_marginal_entropy_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:16:01.219838+00:00
-- url     : https://prove2.me/submissions/e34e9941-d29a-46ea-a417-8c1488e1030a

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_same_marginal_entropy_minimal
import Theorems.Thm_mme_stothers_phi233_orbit_entropy_symmetrization
import Theorems.Thm_mme_stothers_phi233_orbit_average_constraints

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

theorem solution
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      ∀ x : Fin 10 → ℝ,
        (∀ r, 0 ≤ x r) →
        (∑ r : Fin 10, x r) = 1 →
        x 0 + x 1 + x 2 = sigma / 2 →
        x 7 + x 8 + x 9 = sigma / 2 →
        x 3 + x 7 = mu / 2 →
        x 2 + x 6 = mu / 2 →
        x 6 + x 9 = mu / 2 →
        x 0 + x 3 = mu / 2 →
        (∑ r : Fin 10, Real.negMulLog (x r)) ≤
          4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) := by
  dsimp
  obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd, hab, hac, hmin⟩ :=
    mme_stothers_phi233_same_marginal_entropy_minimal
      E H L hE hH hEL hHL
  refine ⟨a, b, c, d, ha, hb, hc, hd, habcd, hab, hac, ?_⟩
  intro x hx htotal hsigma0 hsigma2 hmuJ0 hmuJ3 hmuK0 hmuK3
  let A := (x 0 + x 2 + x 7 + x 9) / 2
  let B := x 1 + x 8
  let C := x 3 + x 6
  let D := x 4 + x 5
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [hx 0, hx 2, hx 7, hx 9]
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [hx 1, hx 8]
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [hx 3, hx 6]
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith [hx 4, hx 5]
  have horbitConstraints :=
    mme_stothers_phi233_orbit_average_constraints
      x (2 * H / (2 * H + L)) (E / (E + L))
      htotal hsigma0 hsigma2 hmuJ0 hmuJ3 hmuK0 hmuK3
  dsimp only at horbitConstraints
  have hABCD : 2 * A + B + C + D = 1 := by
    simpa only [A, B, C, D] using horbitConstraints.1
  have hAB : 2 * A + B = 2 * H / (2 * H + L) := by
    simpa only [A, B, C, D] using horbitConstraints.2.1
  have hAC : A + C = E / (E + L) := by
    simpa only [A, B, C, D] using horbitConstraints.2.2
  have hcost := hmin A B C D hA hB hC hD hABCD hAB hAC
  have hbase :
      2 * Real.negMulLog A + Real.negMulLog B +
          Real.negMulLog C + Real.negMulLog D ≤
        2 * Real.negMulLog a + Real.negMulLog b +
          Real.negMulLog c + Real.negMulLog d := by
    linarith
  have hhalf (z : ℝ) :
      Real.negMulLog (z / 2) =
        (1 / 2 : ℝ) * Real.negMulLog z +
          z * Real.negMulLog (1 / 2 : ℝ) := by
    rw [show z / 2 = z * (1 / 2 : ℝ) by ring,
      Real.negMulLog_mul]
  have hOrbitExpand :
      4 * Real.negMulLog (A / 2) +
          2 * Real.negMulLog (B / 2) +
          2 * Real.negMulLog (C / 2) +
          2 * Real.negMulLog (D / 2) =
        2 * Real.negMulLog A + Real.negMulLog B +
          Real.negMulLog C + Real.negMulLog D +
          2 * Real.negMulLog (1 / 2 : ℝ) := by
    calc
      _ = 2 * Real.negMulLog A + Real.negMulLog B +
            Real.negMulLog C + Real.negMulLog D +
            2 * (2 * A + B + C + D) *
              Real.negMulLog (1 / 2 : ℝ) := by
          rw [hhalf A, hhalf B, hhalf C, hhalf D]
          ring
      _ = _ := by rw [hABCD]; ring
  have hTargetExpand :
      4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) =
        2 * Real.negMulLog a + Real.negMulLog b +
          Real.negMulLog c + Real.negMulLog d +
          2 * Real.negMulLog (1 / 2 : ℝ) := by
    calc
      _ = 2 * Real.negMulLog a + Real.negMulLog b +
            Real.negMulLog c + Real.negMulLog d +
            2 * (2 * a + b + c + d) *
              Real.negMulLog (1 / 2 : ℝ) := by
          rw [hhalf a, hhalf b, hhalf c, hhalf d]
          ring
      _ = _ := by rw [habcd]; ring
  have horbit := mme_stothers_phi233_orbit_entropy_symmetrization x hx
  have hOrbitRewrite :
      4 * Real.negMulLog ((x 0 + x 2 + x 7 + x 9) / 4) +
          2 * Real.negMulLog ((x 1 + x 8) / 2) +
          2 * Real.negMulLog ((x 3 + x 6) / 2) +
          2 * Real.negMulLog ((x 4 + x 5) / 2) =
        4 * Real.negMulLog (A / 2) +
          2 * Real.negMulLog (B / 2) +
          2 * Real.negMulLog (C / 2) +
          2 * Real.negMulLog (D / 2) := by
    have hAarg : (x 0 + x 2 + x 7 + x 9) / 4 = A / 2 := by
      dsimp [A]
      ring
    have hBarg : (x 1 + x 8) / 2 = B / 2 := by rfl
    have hCarg : (x 3 + x 6) / 2 = C / 2 := by rfl
    have hDarg : (x 4 + x 5) / 2 = D / 2 := by rfl
    rw [hAarg, hBarg, hCarg, hDarg]
  rw [hOrbitRewrite, hOrbitExpand] at horbit
  rw [hTargetExpand]
  linarith
