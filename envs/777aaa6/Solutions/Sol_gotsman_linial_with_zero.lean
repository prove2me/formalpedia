-- Prove2me | solution 1 for gotsman_linial_with_zero
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T20:45:34.812594+00:00
-- url     : https://prove2.me/submissions/6863ae57-3220-4472-9cee-667219ec90ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_gotsman_linial_with_zero
import Theorems.Thm_polyDegree_alternating_sum_witness
import Theorems.Thm_bool_func_alternating_sum_sensitivity
import Definitions.Def_Hypercube
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Tactic.Linarith

/-!
# Sketch — `gotsman_linial_with_zero`

Two cases on `polyDegree f`:

* `polyDegree f = 0`: by `h0`, `h 0 ≤ 0 ≤ sensitivity f`.
* `polyDegree f ≥ 1`: Child B (`polyDegree_alternating_sum_witness`)
  gives an `S` of size `polyDegree f` with non-zero Möbius alternating
  sum on `f`. Child C (`bool_func_alternating_sum_sensitivity`)
  then yields `h S.card ≤ sensitivity f`. Substituting
  `S.card = polyDegree f` closes the goal.
-/

theorem solution
    (h : ℕ → ℝ) (hmono : Monotone h) (h0 : h 0 ≤ 0)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool), 2 ^ (m - 1) < S.card →
        ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {n : ℕ} (f : BoolFunc n) :
    h (polyDegree f) ≤ (sensitivity f : ℝ) := by
  classical
  by_cases hd : polyDegree f = 0
  · -- Constant case: h 0 ≤ 0 ≤ sensitivity f.
    rw [hd]
    have h_sens_nn : (0 : ℝ) ≤ (sensitivity f : ℝ) := Nat.cast_nonneg _
    linarith
  -- polyDegree f ≥ 1.
  have h_pos : 1 ≤ polyDegree f := Nat.one_le_iff_ne_zero.mpr hd
  obtain ⟨S, hS_card, hS_alt⟩ :=
    polyDegree_alternating_sum_witness f h_pos
  have h_S_pos : 1 ≤ S.card := hS_card.symm ▸ h_pos
  have h_bound :=
    bool_func_alternating_sum_sensitivity h hmono hQ f S h_S_pos hS_alt
  rw [hS_card] at h_bound
  exact h_bound
