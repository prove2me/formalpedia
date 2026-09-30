-- Prove2me | solution 1 for Hirsch.vertex_exposing_redundant_row_extension
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T19:47:33.138514+00:00
-- url     : https://prove2.me/submissions/5d388412-08c4-4b24-a60a-950a34fc0cb5

import Definitions.Def_Hirsch_model
import Mathlib
-- BEGIN Solutions/PolynomialVertexSpan.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

namespace HirschPolynomialAccess

/-- A direct finite-perturbation proof, with no imported theorem stubs.
A direction annihilating all inequalities active at a vertex must be zero. -/
theorem vertex_tight_rows_span_checked
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
    · have hs : 0 < b i - ⟪a i, x⟫ := sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
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


end HirschPolynomialAccess

-- BEGIN Solutions/PolynomialVertexExposingRow.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExposure

/-- The sum of rows active at a vertex exposes precisely that vertex.
A distinct feasible point ensures the exposing normal is nonzero. Boundedness
and irredundancy are unnecessary. -/
theorem exposing_row_from_active_sum
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) :
    ∃ (c : EuclideanSpace ℝ (Fin d)) (β : ℝ),
      c ≠ 0 ∧ ⟪c, v⟫ = β ∧ ⟪c, u⟫ < β ∧
      (∀ x ∈ Hpoly a b, ⟪c, x⟫ ≤ β) ∧
      (∀ x ∈ Hpoly a b, ⟪c, x⟫ = β ↔ x = v) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)
  let c : EuclideanSpace ℝ (Fin d) := ∑ i ∈ S, a i
  let β : ℝ := ∑ i ∈ S, b i
  have hcv : ⟪c, v⟫ = β := by
    dsimp [c, β]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hle : ∀ x ∈ Hpoly a b, ⟪c, x⟫ ≤ β := by
    intro x hx
    dsimp [c, β]
    rw [sum_inner]
    exact Finset.sum_le_sum (fun i _ => hx i)
  have heq : ∀ x ∈ Hpoly a b, ⟪c, x⟫ = β ↔ x = v := by
    intro x hx
    constructor
    · intro hcx
      have hsum : (∑ i ∈ S, (b i - ⟪a i, x⟫)) = 0 := by
        rw [Finset.sum_sub_distrib]
        have hsuminner : (∑ i ∈ S, ⟪a i, x⟫) = ⟪c, x⟫ := by
          dsimp [c]
          rw [sum_inner]
        rw [hsuminner]
        exact sub_eq_zero.mpr hcx.symm
      have hall : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, x⟫ = b i := by
        intro i hit
        have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hit⟩
        have hi_le : b i - ⟪a i, x⟫ ≤ ∑ j ∈ S, (b j - ⟪a j, x⟫) :=
          Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hx j)) hiS
        rw [hsum] at hi_le
        linarith [hx i]
      have horth : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, x - v⟫ = 0 := by
        intro i hit
        rw [inner_sub_right, hall i hit, hit, sub_self]
      exact sub_eq_zero.mp (vertex_tight_rows_span_checked d n a b v hv (x - v) horth)
    · intro h
      rw [h]
      exact hcv
  have hc : c ≠ 0 := by
    intro hc0
    have hcu : ⟪c, u⟫ = β := by
      have hb0 : β = 0 := by simpa only [hc0, inner_zero_left] using hcv.symm
      rw [hc0, inner_zero_left, hb0]
    exact huv ((heq u hu).1 hcu)
  have hult : ⟪c, u⟫ < β :=
    lt_of_le_of_ne (hle u hu) (fun h => huv ((heq u hu).1 h))
  exact ⟨c, β, hc, hcv, hult, hle, heq⟩


end HirschExposure
end


-- BEGIN Solutions/PolynomialVertexExposureSubmission.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschExposure

set_option maxHeartbeats 3000000

noncomputable section

/-- Add one redundant inequality exposing exactly v. The original inequalities,
polytope, and graph are unchanged; the added row is a target row, never neutral.
Endpoint separation is preserved. Thus prescribed supporting-row access may
literally require reaching v, even without adding any neutral normals. -/
theorem solution
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (b' : Fin (n + 1) → ℝ),
      (∀ j : Fin n, a' j.castSucc = a j ∧ b' j.castSucc = b j) ∧
      Hpoly a' b' = Hpoly a b ∧
      a' (Fin.last n) ≠ 0 ∧
      ⟪a' (Fin.last n), v⟫ = b' (Fin.last n) ∧
      ⟪a' (Fin.last n), u⟫ < b' (Fin.last n) ∧
      (∀ x ∈ Hpoly a' b', ⟪a' (Fin.last n), x⟫ = b' (Fin.last n) ↔ x = v) ∧
      (∀ j, a' j ≠ 0 → ⟪a' j, u⟫ ≠ b' j ∨ ⟪a' j, v⟫ ≠ b' j) := by
  obtain ⟨c, β, hc, hcv, hcu, hle, heq⟩ :=
    exposing_row_from_active_sum d n a b u v hu hv huv
  let a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d) := Fin.snoc a c
  let b' : Fin (n + 1) → ℝ := Fin.snoc b β
  have hrows : ∀ j : Fin n, a' j.castSucc = a j ∧ b' j.castSucc = b j := by
    intro j
    simp [a', b']
  have halast : a' (Fin.last n) = c := by simp [a']
  have hblast : b' (Fin.last n) = β := by simp [b']
  have hpoly : Hpoly a' b' = Hpoly a b := by
    ext x
    constructor
    · intro hx j
      have h := hx j.castSucc
      rw [(hrows j).1, (hrows j).2] at h
      exact h
    · intro hx j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [halast, hblast]
        exact hle x hx
      · rw [(hrows k).1, (hrows k).2]
        exact hx k
  refine ⟨a', b', hrows, hpoly, ?_, ?_, ?_, ?_, ?_⟩
  · rw [halast]
    exact hc
  · rw [halast, hblast]
    exact hcv
  · rw [halast, hblast]
    exact hcu
  · intro x hx
    rw [halast, hblast]
    exact heq x (hpoly ▸ hx)
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro _
      left
      rw [halast, hblast]
      exact ne_of_lt hcu
    · intro haj
      have hak : a k ≠ 0 := by simpa only [(hrows k).1] using haj
      simpa only [(hrows k).1, (hrows k).2] using hsep k hak

end


#print axioms solution
