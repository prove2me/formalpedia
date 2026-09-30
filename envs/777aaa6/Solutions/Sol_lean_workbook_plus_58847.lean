-- Prove2me | solution 1 for lean_workbook_plus_58847
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:40.421337+00:00
-- url     : https://prove2.me/submissions/0a9ddbeb-4f6a-47d5-811d-2cb163da2341

import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

namespace PairwiseDistanceConeClassification

def Condition (C : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y, f x + f y ≤ 2 * C - |x - y|

theorem endpoint_bound {C : ℝ} {f : ℝ → ℝ} (h : Condition C f) (x y : ℝ) :
    x + f x - C ≤ y - f y + C := by
  have hxy := h x y
  have habs := le_abs_self (x - y)
  linarith

theorem common_center {C : ℝ} {f : ℝ → ℝ} (h : Condition C f) :
    ∃ c, ∀ x, x + f x - C ≤ c ∧ c ≤ x - f x + C := by
  let A : Set ℝ := Set.range (fun x => x + f x - C)
  have hne : A.Nonempty := ⟨0 + f 0 - C, ⟨0, rfl⟩⟩
  have hb : BddAbove A := by
    refine ⟨0 - f 0 + C, ?_⟩
    rintro a ⟨x, rfl⟩
    exact endpoint_bound h x 0
  refine ⟨sSup A, fun x => ⟨le_csSup hb ⟨x, rfl⟩, ?_⟩⟩
  apply csSup_le hne
  rintro a ⟨y, rfl⟩
  exact endpoint_bound h y x

theorem below_cone_satisfies {C c : ℝ} {f : ℝ → ℝ}
    (h : ∀ x, f x ≤ C - |x - c|) : Condition C f := by
  intro x y
  have ht := abs_sub_le x c y
  rw [abs_sub_comm c y] at ht
  linarith [h x, h y]

theorem full_classification (C : ℝ) (f : ℝ → ℝ) :
    Condition C f ↔ ∃ c, ∀ x, f x ≤ C - |x - c| := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := common_center h
    refine ⟨c, fun x => ?_⟩
    have hx := hc x
    have ha : |x - c| ≤ C - f x := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  · rintro ⟨c, hc⟩
    exact below_cone_satisfies hc

theorem defect_parametrization (C : ℝ) (f : ℝ → ℝ) :
    Condition C f ↔ ∃ (c : ℝ) (d : ℝ → ℝ), (∀ x, 0 ≤ d x) ∧
      ∀ x, f x = C - |x - c| - d x := by
  rw [full_classification]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x => C - |x - c| - f x, ?_, ?_⟩
    · intro x
      linarith [hc x]
    · intro x
      dsimp
      linarith
  · rintro ⟨c, d, hd, hf⟩
    refine ⟨c, fun x => ?_⟩
    rw [hf x]
    linarith [hd x]

theorem source_bound {C : ℝ} {f : ℝ → ℝ} (h : Condition C f) (x : ℝ) :
    f x ≤ C := by
  obtain ⟨c, hc⟩ := (full_classification C f).1 h
  linarith [hc x, abs_nonneg (x - c)]

theorem attaining_point_determines_center {C : ℝ} {f : ℝ → ℝ}
    (h : Condition C f) {a : ℝ} (ha : f a = C) :
    (∀ x, f x ≤ C - |x - a|) ∧ ∀ b, f b = C → b = a := by
  obtain ⟨c, hc⟩ := (full_classification C f).1 h
  have hac : a = c := by
    have h0 : |a - c| = 0 := le_antisymm (by linarith [hc a]) (abs_nonneg _)
    exact sub_eq_zero.1 (abs_eq_zero.1 h0)
  subst c
  refine ⟨hc, fun b hb => ?_⟩
  have h0 : |b - a| = 0 := le_antisymm (by linarith [hc b]) (abs_nonneg _)
  exact sub_eq_zero.1 (abs_eq_zero.1 h0)

theorem sharp_models (C c : ℝ) :
    Condition C (fun x => C - |x - c|) ∧
      (∀ x, C - |x - c| = C ↔ x = c) := by
  refine ⟨below_cone_satisfies (fun _ => le_rfl), ?_⟩
  intro x
  constructor
  · intro h
    exact sub_eq_zero.1 (abs_eq_zero.1 (by linarith : |x - c| = 0))
  · intro h
    simp [h]

end PairwiseDistanceConeClassification

theorem solution (f : ℝ → ℝ)
    (h : ∀ x y : ℝ, f x + f y ≤ 2 - abs (x - y)) : ∀ x : ℝ, f x ≤ 1 := by
  have hc : PairwiseDistanceConeClassification.Condition 1 f := by
    unfold PairwiseDistanceConeClassification.Condition
    simpa only [mul_one] using h
  exact PairwiseDistanceConeClassification.source_bound hc
