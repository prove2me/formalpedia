-- Prove2me | solution 1 for BookSixth.uniform_nonincident_clearance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T16:37:52.507777+00:00
-- url     : https://prove2.me/submissions/1e4f9360-49c8-402b-8154-06154f65ae6c

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

/- Clearance candidate, not a proof of the edge bound.
   All distances use the canonical metric on Fin 2 -> Real. No exponents occur.
   The uniform radius is derived, not an extra hypothesis on PlaneDrawing. -/

private theorem arc_ne_nonincident_vertex {N M : ℕ} (D : PlaneDrawing N M)
    (v : Fin N) (e : Fin M) (hl : D.left e ≠ v) (hr : D.right e ≠ v)
    (t : EdgeParameter) : D.arc e t ≠ D.vertex v := by
  intro heq
  by_cases ht0 : t.val = 0
  · have ht : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht0
    rw [ht, D.start] at heq
    exact hl (D.vertex_injective heq)
  by_cases ht1 : t.val = 1
  · have ht : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht1
    rw [ht, D.finish] at heq
    exact hr (D.vertex_injective heq)
  exact D.avoid_vertices e t
    (lt_of_le_of_ne t.property.1 (Ne.symm ht0))
    (lt_of_le_of_ne t.property.2 ht1) v heq

private theorem pair_clearance {N M : ℕ} (D : PlaneDrawing N M)
    (v : Fin N) (e : Fin M) (hl : D.left e ≠ v) (hr : D.right e ≠ v) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : EdgeParameter,
      r < dist (D.arc e t) (D.vertex v) := by
  have hc : Continuous (fun t : EdgeParameter => dist (D.arc e t) (D.vertex v)) :=
    (D.continuous_arc e).dist continuous_const
  obtain ⟨a, ha, hbound⟩ := isCompact_univ.exists_forall_le' hc.continuousOn
    (fun t _ => dist_pos.mpr (arc_ne_nonincident_vertex D v e hl hr t))
  refine ⟨a / 2, half_pos ha, fun t => ?_⟩
  exact (half_lt_self ha).trans_le (hbound t (Set.mem_univ t))

theorem solution {N M : ℕ} (D : PlaneDrawing N M) :
    ∃ r : ℝ, 0 < r ∧ ∀ (v : Fin N) (e : Fin M),
      D.left e ≠ v → D.right e ≠ v → ∀ t : EdgeParameter,
        r < dist (D.arc e t) (D.vertex v) := by
  classical
  have finite_clearance (S : Finset (Fin N × Fin M)) :
      ∃ r : ℝ, 0 < r ∧ ∀ p ∈ S,
        D.left p.2 ≠ p.1 → D.right p.2 ≠ p.1 → ∀ t : EdgeParameter,
          r < dist (D.arc p.2 t) (D.vertex p.1) := by
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨1, zero_lt_one, by simp⟩
    | @insert p S hp ih =>
        obtain ⟨r, hr, hS⟩ := ih
        by_cases hinc : D.left p.2 ≠ p.1 ∧ D.right p.2 ≠ p.1
        · obtain ⟨a, ha, hpa⟩ := pair_clearance D p.1 p.2 hinc.1 hinc.2
          refine ⟨min r a, lt_min hr ha, ?_⟩
          intro q hq hl hright t
          rcases Finset.mem_insert.mp hq with heq | hq
          · subst q
            exact (min_le_right r a).trans_lt (hpa t)
          · exact (min_le_left r a).trans_lt (hS q hq hl hright t)
        · refine ⟨r, hr, ?_⟩
          intro q hq hl hright t
          rcases Finset.mem_insert.mp hq with heq | hq
          · subst q
            exact False.elim (hinc ⟨hl, hright⟩)
          · exact hS q hq hl hright t
  obtain ⟨r, hr, hbound⟩ := finite_clearance Finset.univ
  exact ⟨r, hr, fun v e => hbound (v, e) (Finset.mem_univ _)⟩
