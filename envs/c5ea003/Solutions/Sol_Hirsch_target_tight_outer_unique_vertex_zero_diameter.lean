-- Prove2me | solution 1 for Hirsch.target_tight_outer_unique_vertex_zero_diameter
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T05:24:31.140256+00:00
-- url     : https://prove2.me/submissions/9903527d-a915-4c03-9109-5142f582d801

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Hirsch

/-- Direct finite-perturbation fact used by the public target-tight theorem:
rows tight at a vertex span the ambient direction space. -/
private theorem targetTight_vertex_tight_rows_span
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (y : EuclideanSpace ℝ (Fin d))
    (horth : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hp : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hm : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

/-- Every vertex of a finite H-polyhedron has a subpresentation made from
exactly the inequalities tight at that vertex. In that relaxed outer the chosen
point is the unique vertex, so its padded vertex-edge graph diameter is zero.

The outer may be unbounded and may contain infinitely many nonvertex points.
No boundedness, irredundancy, or full-dimensionality assumption is used. -/
theorem target_tight_outer_unique_vertex_zero_diameter
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i) ∧
      extremePoints ℝ (Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} ∧
      DiamLE (Hpoly (fun k => a (e k)) (fun k => b (e k))) 0 := by
  classical
  let I := {i : Fin n // ⟪a i, v⟫ = b i}
  let m := Fintype.card I
  let φ : Fin m ≃ I := (Fintype.equivFin I).symm
  let e : Fin m ↪ Fin n :=
    ⟨fun k => (φ k).1, fun p q h => φ.injective (Subtype.ext h)⟩
  have hm : m ≤ n := by
    dsimp [m, I]
    have hcard := Fintype.card_le_of_injective
      (fun i : {i : Fin n // ⟪a i, v⟫ = b i} => i.1)
      (fun x y h => Subtype.ext h)
    simpa only [Fintype.card_fin] using hcard
  have hrange : ∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i := by
    intro i
    constructor
    · rintro ⟨k, rfl⟩
      exact (φ k).2
    · intro hi
      refine ⟨φ.symm ⟨i, hi⟩, ?_⟩
      simp [e]
  have htight : ∀ k, ⟪a (e k), v⟫ = b (e k) := by
    intro k
    exact (hrange (e k)).1 ⟨k, rfl⟩
  let Q := Hpoly (fun k => a (e k)) (fun k => b (e k))
  have hvQ : v ∈ extremePoints ℝ Q := by
    refine ⟨?_, ?_⟩
    · intro k
      exact le_of_eq (htight k)
    · intro p hp q hq hseg
      obtain ⟨α, β, hα, hβ, hsum, hcomb⟩ := hseg
      apply sub_eq_zero.mp
      apply targetTight_vertex_tight_rows_span d n a b v hv (p - v)
      intro i hi
      obtain ⟨k, hk⟩ := (hrange i).2 hi
      have hp_le : ⟪a i, p⟫ ≤ b i := by
        simpa only [hk] using hp k
      have hq_le : ⟪a i, q⟫ ≤ b i := by
        simpa only [hk] using hq k
      have heval := congrArg
        (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) hcomb
      simp only [inner_add_right, inner_smul_right] at heval
      have hb : α * b i + β * b i = b i := by
        rw [← add_mul, hsum, one_mul]
      have hp_eq : ⟪a i, p⟫ = b i := by
        by_contra hne
        have hlt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hne
        have h1 := mul_lt_mul_of_pos_left hlt hα
        have h2 := mul_le_mul_of_nonneg_left hq_le hβ.le
        rw [hi] at heval
        linarith
      rw [inner_sub_right, hp_eq, hi, sub_self]
  have hverts : extremePoints ℝ Q = {v} := by
    ext z
    constructor
    · intro hz
      apply Set.mem_singleton_iff.mpr
      apply sub_eq_zero.mp
      apply targetTight_vertex_tight_rows_span d m
        (fun k => a (e k)) (fun k => b (e k)) z hz (z - v)
      intro k hk
      change ⟪a (e k), z - v⟫ = 0
      rw [inner_sub_right, hk, htight k, sub_self]
    · intro hz
      have hzv : z = v := Set.mem_singleton_iff.mp hz
      subst z
      exact hvQ
  have hdiam : DiamLE Q 0 := by
    intro p hp q hq
    rw [hverts] at hp hq
    have hpv : p = v := Set.mem_singleton_iff.mp hp
    have hqv : q = v := Set.mem_singleton_iff.mp hq
    subst p
    subst q
    exact ⟨fun _ => v, rfl, rfl, by intro j hj; omega⟩
  exact ⟨m, hm, e, hrange, hverts, hdiam⟩

#print axioms target_tight_outer_unique_vertex_zero_diameter

end Hirsch


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i) ∧
      Set.extremePoints ℝ (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} ∧
      Hirsch.DiamLE (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) 0 := by
  exact Hirsch.target_tight_outer_unique_vertex_zero_diameter a b v hv

#print axioms solution
