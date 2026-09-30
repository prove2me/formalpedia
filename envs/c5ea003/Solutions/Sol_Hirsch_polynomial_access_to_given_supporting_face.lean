-- Prove2me | solution 1 for Hirsch.polynomial_access_to_given_supporting_face
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T16:06:42.04545+00:00
-- url     : https://prove2.me/submissions/7b01aa51-f037-4829-bf33-962b8e5e4f43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hirsch_cubic_circuit_walk_bound
import Theorems.Thm_Hirsch_polynomial_edge_refinement_of_circuit_walks

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Hirsch

/-- An exact-type sketch of the existing prescribed-supporting-face leaf.
Both imported children are assumptions of this sketch. The first is a known
circuit theorem plus presentation normalization; the second is open research. -/
theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ Set.extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨Cc, hc⟩ := Hirsch.cubic_circuit_walk_bound
  obtain ⟨Ce, ke, he⟩ := Hirsch.polynomial_edge_refinement_of_circuit_walks
  refine ⟨Ce * Cc, ke + 3, ?_⟩
  intro d n a b hbd u hu v hv _huv hsep i _hai hiv
  obtain ⟨m, hmn, e, hP, hirr, hstrict, hcwalk⟩ := hc d n a b hbd u hu v hv hsep
  have hbd' : Bornology.IsBounded
      (Hpoly (fun j => a (e j)) (fun j => b (e j))) := by
    simpa only [hP] using hbd
  have hu' : u ∈ Set.extremePoints ℝ
      (Hpoly (fun j => a (e j)) (fun j => b (e j))) := by
    simpa only [hP] using hu
  have hv' : v ∈ Set.extremePoints ℝ
      (Hpoly (fun j => a (e j)) (fun j => b (e j))) := by
    simpa only [hP] using hv
  obtain ⟨w, hw0, hwB, hwstep⟩ :=
    he d m (fun j => a (e j)) (fun j => b (e j)) hbd' hirr hstrict
      u hu' v hv' (Cc * (m + d) ^ 3) hcwalk
  let B : ℕ := Ce * (m + d) ^ ke * (Cc * (m + d) ^ 3)
  let D : ℕ := (Ce * Cc) * (n + d) ^ (ke + 3)
  have hBform : B = (Ce * Cc) * (m + d) ^ (ke + 3) := by
    dsimp [B]
    rw [pow_add]
    ring
  have hBD : B ≤ D := by
    rw [hBform]
    exact Nat.mul_le_mul_left (Ce * Cc)
      (Nat.pow_le_pow_left (by omega : m + d ≤ n + d) (ke + 3))
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (min j B)
  refine ⟨v, hv, hiv, wp, ?_, ?_, ?_⟩
  · change w (min 0 B) = u
    simpa only [Nat.zero_min] using hw0
  · change w (min D B) = v
    rw [Nat.min_eq_right hBD]
    exact hwB
  · intro j hj
    by_cases hjB : j < B
    · have hjle : j ≤ B := Nat.le_of_lt hjB
      have hj1le : j + 1 ≤ B := by omega
      simpa only [wp, Nat.min_eq_left hjle, Nat.min_eq_left hj1le, hP]
        using hwstep j hjB
    · have hBj : B ≤ j := by omega
      have hBj1 : B ≤ j + 1 := by omega
      exact Or.inl (by simp only [wp, Nat.min_eq_right hBj, Nat.min_eq_right hBj1])

#print axioms solution
