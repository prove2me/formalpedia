-- Prove2me | solution 1 for lean_workbook_plus_34658
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:11:55.383355+00:00
-- url     : https://prove2.me/submissions/b756b87b-f28f-4c73-b79b-06a6937a0011

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

inductive PolygonalExpr where
  | affine (slope intercept : ℝ)
  | join (left right : PolygonalExpr)
  | meet (left right : PolygonalExpr)

noncomputable def PolygonalExpr.eval : PolygonalExpr → ℝ → ℝ
  | .affine a b, x => a * x + b
  | .join p q, x => max (p.eval x) (q.eval x)
  | .meet p q, x => min (p.eval x) (q.eval x)

theorem PolygonalExpr.continuous (e : PolygonalExpr) : Continuous e.eval := by
  induction e with
  | affine a b => exact (continuous_const.mul continuous_id).add continuous_const
  | join p q hp hq => exact hp.max hq
  | meet p q hp hq => exact hp.min hq

theorem PolygonalExpr.finite_affine_pieces (e : PolygonalExpr) :
    ∃ pieces : Finset (ℝ × ℝ), ∀ x : ℝ,
      ∃ ab ∈ pieces, e.eval x = ab.1 * x + ab.2 := by
  classical
  induction e with
  | affine a b =>
      exact ⟨{(a, b)}, fun x => ⟨(a, b), Finset.mem_singleton_self _, rfl⟩⟩
  | join p q hp hq =>
      obtain ⟨ps, hps⟩ := hp
      obtain ⟨qs, hqs⟩ := hq
      refine ⟨ps ∪ qs, fun x => ?_⟩
      rcases le_total (p.eval x) (q.eval x) with h | h
      · obtain ⟨ab, hab, hx⟩ := hqs x
        exact ⟨ab, Finset.mem_union_right _ hab, (max_eq_right h).trans hx⟩
      · obtain ⟨ab, hab, hx⟩ := hps x
        exact ⟨ab, Finset.mem_union_left _ hab, (max_eq_left h).trans hx⟩
  | meet p q hp hq =>
      obtain ⟨ps, hps⟩ := hp
      obtain ⟨qs, hqs⟩ := hq
      refine ⟨ps ∪ qs, fun x => ?_⟩
      rcases le_total (p.eval x) (q.eval x) with h | h
      · obtain ⟨ab, hab, hx⟩ := hps x
        exact ⟨ab, Finset.mem_union_left _ hab, (min_eq_left h).trans hx⟩
      · obtain ⟨ab, hab, hx⟩ := hqs x
        exact ⟨ab, Finset.mem_union_right _ hab, (min_eq_right h).trans hx⟩

noncomputable def PolygonalExpr.onSet (s : Set ℝ) (e : PolygonalExpr) : C(s, ℝ) :=
  ⟨fun x => e.eval x, e.continuous.comp continuous_subtype_val⟩

theorem polygonal_closure (a b : ℝ) :
    closure (Set.range (PolygonalExpr.onSet (Set.Icc a b))) = Set.univ := by
  let L : Set C(Set.Icc a b, ℝ) := Set.range (PolygonalExpr.onSet (Set.Icc a b))
  apply ContinuousMap.sublattice_closure_eq_top L
  · exact ⟨PolygonalExpr.onSet _ (.affine 0 0), ⟨.affine 0 0, rfl⟩⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    refine ⟨.meet p q, ?_⟩
    ext x
    rfl
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    refine ⟨.join p q, ?_⟩
    ext x
    rfl
  · intro v x y
    by_cases hxy : x = y
    · subst y
      refine ⟨PolygonalExpr.onSet _ (.affine 0 (v x)), ⟨.affine 0 (v x), rfl⟩, ?_, ?_⟩
      all_goals change 0 * (x : ℝ) + v x = v x; ring
    · have hne : (x : ℝ) - (y : ℝ) ≠ 0 := sub_ne_zero.mpr fun h => hxy (Subtype.ext h)
      let m : ℝ := (v x - v y) / ((x : ℝ) - (y : ℝ))
      let e : PolygonalExpr := .affine m (v y - m * (y : ℝ))
      refine ⟨PolygonalExpr.onSet _ e, ⟨e, rfl⟩, ?_, ?_⟩
      · change m * (x : ℝ) + (v y - m * (y : ℝ)) = v x
        dsimp [m]
        field_simp
        ring
      · change m * (y : ℝ) + (v y - m * (y : ℝ)) = v y
        ring

theorem polygonal_uniform_approximation (f : ℝ → ℝ) (a b ε : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hε : 0 < ε) :
    ∃ e : PolygonalExpr, ∀ x ∈ Set.Icc a b, |f x - e.eval x| < ε := by
  let F : C(Set.Icc a b, ℝ) :=
    ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  have hclosure : F ∈ closure (Set.range (PolygonalExpr.onSet (Set.Icc a b))) := by
    rw [polygonal_closure]
    trivial
  obtain ⟨g, ⟨e, rfl⟩, he⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  refine ⟨e, fun x hx => ?_⟩
  have hdist := (ContinuousMap.dist_apply_le_dist (f := F)
    (g := PolygonalExpr.onSet _ e) ⟨x, hx⟩).trans_lt he
  exact hdist

theorem solution (f : ℝ → ℝ) (a b : ℝ) (ε : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, |f x - ψ x| < ε := by
  obtain ⟨e, he⟩ := polygonal_uniform_approximation f a b ε hf hε
  exact ⟨e.eval, e.continuous.continuousOn, he⟩

#print axioms PolygonalExpr.finite_affine_pieces
#print axioms polygonal_closure
#print axioms polygonal_uniform_approximation
#print axioms solution
