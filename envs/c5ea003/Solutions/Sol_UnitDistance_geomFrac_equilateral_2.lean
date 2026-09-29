-- Prove2me | solution 2 for UnitDistance.geomFrac_equilateral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:39:02.040667+00:00
-- url     : https://prove2.me/submissions/9a1f5d8c-debf-41aa-b4bc-b1a4e9e0e700

import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
import Definitions.Def_Geometry_UnitDistanceFractional
open SimpleGraph Finset GeomFrac UnitDistance in
theorem solution : geomFrac (unitDistanceGraph equilateral) = 3 := by
  classical
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the three side lengths are all `1`
  have hd01 : dist (equilateral 0) (equilateral 1) = 1 := by
    simp only [equilateral, pt]
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have hd02 : dist (equilateral 0) (equilateral 2) = 1 := by
    simp only [equilateral, pt]
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
    rw [abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, h3]
    norm_num
  have hd12 : dist (equilateral 1) (equilateral 2) = 1 := by
    simp only [equilateral, pt]
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
    rw [abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, h3, Real.dist_eq]
    norm_num
  -- so the unit-distance graph is complete: any two distinct vertices are adjacent
  have hadj : ∀ u v : Fin 3, u ≠ v → (unitDistanceGraph equilateral).Adj u v := by
    intro u v huv
    refine ⟨huv, ?_⟩
    fin_cases u <;> fin_cases v
    all_goals first
      | exact absurd rfl huv
      | exact hd01 | exact hd02 | exact hd12
      | (rw [_root_.dist_comm]; exact hd01)
      | (rw [_root_.dist_comm]; exact hd02)
      | (rw [_root_.dist_comm]; exact hd12)
  -- hence every independent set has at most one vertex
  have hcard1 : ∀ S : Finset (Fin 3),
      (unitDistanceGraph equilateral).IsIndepSet (S : Set (Fin 3)) → S.card ≤ 1 := by
    intro S hS
    by_contra hlt
    push_neg at hlt
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
    exact hS ha hb hab (hadj a b hab)
  -- LOWER BOUND: every fractional colouring costs at least `3`
  have hlow : ∀ c : FracColoring (unitDistanceGraph equilateral), (3 : ℝ) ≤ c.total := by
    intro c
    have hcount : ∑ v : Fin 3, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => v ∈ S), c.weight S
        = ∑ S : Finset (Fin 3), (S.card : ℝ) * c.weight S := by
      have hinner : ∀ S : Finset (Fin 3),
          (∑ _v ∈ S, c.weight S) = (S.card : ℝ) * c.weight S := by
        intro S
        rw [Finset.sum_const, nsmul_eq_mul]
      calc ∑ v : Fin 3, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => v ∈ S), c.weight S
          = ∑ v : Fin 3, ∑ S : Finset (Fin 3), (if v ∈ S then c.weight S else 0) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.sum_filter]
        _ = ∑ S : Finset (Fin 3), ∑ v : Fin 3, (if v ∈ S then c.weight S else 0) :=
            Finset.sum_comm
        _ = ∑ S : Finset (Fin 3), (S.card : ℝ) * c.weight S := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.sum_ite_mem, Finset.univ_inter, hinner S]
    have hstep : ∀ S : Finset (Fin 3), (S.card : ℝ) * c.weight S ≤ c.weight S := by
      intro S
      by_cases hw : c.weight S = 0
      · rw [hw]; simp
      · have hindep : (unitDistanceGraph equilateral).IsIndepSet (S : Set (Fin 3)) := by
          by_contra hc
          exact hw (c.supp S hc)
        have hc1 : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard1 S hindep
        nlinarith [c.nonneg S]
    calc (3 : ℝ) = ∑ _v : Fin 3, (1 : ℝ) := by simp
      _ ≤ ∑ v : Fin 3, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => v ∈ S), c.weight S :=
          Finset.sum_le_sum fun v _ => c.covers v
      _ = ∑ S : Finset (Fin 3), (S.card : ℝ) * c.weight S := hcount
      _ ≤ ∑ S : Finset (Fin 3), c.weight S := Finset.sum_le_sum fun S _ => hstep S
      _ = c.total := rfl
  -- UPPER BOUND: the singleton colouring costs exactly `3`
  have hsing : (FracColoring.singleton (unitDistanceGraph equilateral)).total = 3 := by
    show ∑ S : Finset (Fin 3), (if S.card = 1 then (1 : ℝ) else 0) = 3
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    norm_cast
  have hne : (Set.range fun c : FracColoring (unitDistanceGraph equilateral) => c.total).Nonempty :=
    ⟨_, Set.mem_range_self (FracColoring.singleton _)⟩
  have hbdd : BddBelow (Set.range fun c : FracColoring (unitDistanceGraph equilateral) => c.total) :=
    ⟨3, by rintro x ⟨c, rfl⟩; exact hlow c⟩
  apply le_antisymm
  · calc geomFrac (unitDistanceGraph equilateral)
        ≤ (FracColoring.singleton (unitDistanceGraph equilateral)).total :=
          csInf_le hbdd (Set.mem_range_self _)
      _ = 3 := hsing
  · exact le_csInf hne (by rintro x ⟨c, rfl⟩; exact hlow c)
