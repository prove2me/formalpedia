-- Prove2me | solution 2 for EmergentGeometry.mmi_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:27:03.089401+00:00
-- url     : https://prove2.me/submissions/dce9065a-2043-4d71-bc2d-ffe04a565c70

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicContractionCalculus
import Definitions.Def_Novelty_HolographicCyclicInequality
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V) (A B C : Region V)
    (hAB : ∀ v, A v = true → B v = false)
    (hBC : ∀ v, B v = true → C v = false)
    (hAC : ∀ v, A v = true → C v = false) :
    entropy M A + entropy M B + entropy M C
        + entropy M (fun v => A v || B v || C v)
      ≤ entropy M (fun v => A v || B v) + entropy M (fun v => B v || C v)
        + entropy M (fun v => A v || C v) := by
  have hcomb : ∀ {m' n' : ℕ} (F : Fin m' → Region V) (H : Fin n' → Region V),
      (∀ u v : V, M.toBulkGraph.weight u v ≠ 0 →
        ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) →
      ∑ i, cutWeight M.toBulkGraph (H i) ≤ ∑ j, cutWeight M.toBulkGraph (F j) := by
    intro m' n' F H h
    -- pointwise comparison of the weighted separation counts
    have hpt : ∀ u v : V,
        ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v
          ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
      intro u v
      by_cases hw : M.toBulkGraph.weight u v = 0
      · simp [hw]
      · have hle : ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ)
            ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) := by
          exact_mod_cast h u v hw
        exact mul_le_mul_of_nonneg_right hle (M.toBulkGraph.weight_nonneg u v)
    -- collect each family into a single double sum
    have hcollect : ∀ {k : ℕ} (K : Fin k → Region V),
        (∑ i, cutWeight M.toBulkGraph (K i))
          = (∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v) / 2 := by
      intro k K
      simp only [cutWeight]
      rw [← Finset.sum_div]
      congr 1
      calc (∑ i, ∑ u : V, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v)
          = ∑ u : V, ∑ i, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
            Finset.sum_comm
        _ = ∑ u : V, ∑ v : V, ∑ i, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
        _ = ∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
            refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
            push_cast
            rw [Finset.sum_mul]
    rw [hcollect H, hcollect F]
    have hsum : (∑ u : V, ∑ v : V, ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v)
        ≤ ∑ u : V, ∑ v : V, ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
    linarith
  have hcontract : ∀ x1 y1 z1 x2 y2 z2 : Bool,
      sepBit (x1 && !y1 && z1) (x2 && !y2 && z2) + sepBit (x1 && y1 && !z1) (x2 && y2 && !z2)
        + sepBit (!x1 && y1 && z1) (!x2 && y2 && z2) + sepBit (x1 || y1 || z1) (x2 || y2 || z2)
        ≤ sepBit x1 x2 + sepBit y1 y2 + sepBit z1 z2 := by decide
  have hbA : ∀ a b c : Bool, (a = true → b = false) → (b = true → c = false) →
      (a = true → c = false) → ((a || b) && !(b || c) && (a || c)) = a := by decide
  have hbB : ∀ a b c : Bool, (a = true → b = false) → (b = true → c = false) →
      (a = true → c = false) → ((a || b) && (b || c) && !(a || c)) = b := by decide
  have hbC : ∀ a b c : Bool, (a = true → b = false) → (b = true → c = false) →
      (a = true → c = false) → (!(a || b) && (b || c) && (a || c)) = c := by decide
  have hbU : ∀ a b c : Bool, ((a || b) || (b || c) || (a || c)) = (a || b || c) := by decide
  obtain ⟨f₁, hf₁, he₁⟩ := Finset.exists_mem_eq_inf'
    (admSet_nonempty M (fun v => A v || B v)) (cutWeight M.toBulkGraph)
  obtain ⟨f₂, hf₂, he₂⟩ := Finset.exists_mem_eq_inf'
    (admSet_nonempty M (fun v => B v || C v)) (cutWeight M.toBulkGraph)
  obtain ⟨f₃, hf₃, he₃⟩ := Finset.exists_mem_eq_inf'
    (admSet_nonempty M (fun v => A v || C v)) (cutWeight M.toBulkGraph)
  have hv1 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hf₁) v hv
  have hv2 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hf₂) v hv
  have hv3 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hf₃) v hv
  have hadmA : (fun v => f₁ v && !(f₂ v) && f₃ v) ∈ admSet M A := by
    rw [mem_admSet]
    intro v hv
    show (f₁ v && !(f₂ v) && f₃ v) = A v
    rw [hv1 v hv, hv2 v hv, hv3 v hv]
    exact hbA (A v) (B v) (C v) (hAB v) (hBC v) (hAC v)
  have hadmB : (fun v => f₁ v && f₂ v && !(f₃ v)) ∈ admSet M B := by
    rw [mem_admSet]
    intro v hv
    show (f₁ v && f₂ v && !(f₃ v)) = B v
    rw [hv1 v hv, hv2 v hv, hv3 v hv]
    exact hbB (A v) (B v) (C v) (hAB v) (hBC v) (hAC v)
  have hadmC : (fun v => !(f₁ v) && f₂ v && f₃ v) ∈ admSet M C := by
    rw [mem_admSet]
    intro v hv
    show (!(f₁ v) && f₂ v && f₃ v) = C v
    rw [hv1 v hv, hv2 v hv, hv3 v hv]
    exact hbC (A v) (B v) (C v) (hAB v) (hBC v) (hAC v)
  have hadmU : (fun v => f₁ v || f₂ v || f₃ v) ∈ admSet M (fun v => A v || B v || C v) := by
    rw [mem_admSet]
    intro v hv
    show (f₁ v || f₂ v || f₃ v) = (A v || B v || C v)
    rw [hv1 v hv, hv2 v hv, hv3 v hv]
    exact hbU (A v) (B v) (C v)
  have key := hcomb ![f₁, f₂, f₃]
    ![fun v => f₁ v && !(f₂ v) && f₃ v, fun v => f₁ v && f₂ v && !(f₃ v),
      fun v => !(f₁ v) && f₂ v && f₃ v, fun v => f₁ v || f₂ v || f₃ v]
    (by
      intro u v _
      simp only [Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      exact hcontract (f₁ u) (f₂ u) (f₃ u) (f₁ v) (f₂ v) (f₃ v))
  have l1 := Finset.inf'_le (cutWeight M.toBulkGraph) hadmA
  have l2 := Finset.inf'_le (cutWeight M.toBulkGraph) hadmB
  have l3 := Finset.inf'_le (cutWeight M.toBulkGraph) hadmC
  have l4 := Finset.inf'_le (cutWeight M.toBulkGraph) hadmU
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons] at key
  simp only [entropy] at *
  linarith
