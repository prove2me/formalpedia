-- Prove2me | solution 2 for EmergentGeometry.mutualInfo_le_two_throat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:33:06.367486+00:00
-- url     : https://prove2.me/submissions/4cf85ceb-c2ad-432d-ade5-0e817ccf9483

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V) {A B : Region V}
    (hAB : Disj A B) :
    mutualInfo M A B ≤ 2 * throat M.toBulkGraph A B := by
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
  have hpt : ∀ m1 f1 m2 f2 : Bool,
      sepBit (m1 && f1) (m2 && f2) + sepBit (m1 && !f1) (m2 && !f2)
        ≤ sepBit m1 m2 + sepBit f1 f2 + sepBit f1 f2 := by decide
  have hBA : ∀ v, B v = true → A v = false := by
    intro v hv
    rcases Bool.eq_false_or_eq_true (A v) with h | h
    · rw [hAB v h] at hv
      exact absurd hv (by simp)
    · exact h
  have hsepne : (sepSet A B).Nonempty := by
    refine ⟨A, ?_⟩
    simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates]
    exact ⟨fun v hv => hv, fun v hv => hBA v hv⟩
  obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_eq_inf' hsepne (cutWeight M.toBulkGraph)
  obtain ⟨m, hm, hme⟩ := Finset.exists_mem_eq_inf'
    (admSet_nonempty M (fun v => A v || B v)) (cutWeight M.toBulkGraph)
  have hfsep := hf
  simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates] at hfsep
  have hadmA : (fun v => m v && f v) ∈ admSet M A := by
    rw [mem_admSet]
    intro v hv
    have hmv : m v = (A v || B v) := (mem_admSet.mp hm) v hv
    show (m v && f v) = A v
    rw [hmv]
    rcases Bool.eq_false_or_eq_true (A v) with hAv | hAv
    · have hfv : f v = true := hfsep.1 v hAv
      have hBv : B v = false := hAB v hAv
      rw [hAv, hBv, hfv]
      simp
    · rcases Bool.eq_false_or_eq_true (B v) with hBv | hBv
      · have hfv : f v = false := hfsep.2 v hBv
        rw [hAv, hBv, hfv]
        simp
      · rw [hAv, hBv]
        simp
  have hadmB : (fun v => m v && !(f v)) ∈ admSet M B := by
    rw [mem_admSet]
    intro v hv
    have hmv : m v = (A v || B v) := (mem_admSet.mp hm) v hv
    show (m v && !(f v)) = B v
    rw [hmv]
    rcases Bool.eq_false_or_eq_true (A v) with hAv | hAv
    · have hfv : f v = true := hfsep.1 v hAv
      have hBv : B v = false := hAB v hAv
      rw [hAv, hBv, hfv]
      simp
    · rcases Bool.eq_false_or_eq_true (B v) with hBv | hBv
      · have hfv : f v = false := hfsep.2 v hBv
        rw [hAv, hBv, hfv]
        simp
      · rw [hAv, hBv]
        simp
  have hkey := hcomb ![m, f, f] ![fun v => m v && f v, fun v => m v && !(f v)]
    (by
      intro u v _
      simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      exact hpt (m u) (f u) (m v) (f v))
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hkey
  have hlA : entropy M A ≤ cutWeight M.toBulkGraph (fun v => m v && f v) :=
    Finset.inf'_le _ hadmA
  have hlB : entropy M B ≤ cutWeight M.toBulkGraph (fun v => m v && !(f v)) :=
    Finset.inf'_le _ hadmB
  have hthroat : throat M.toBulkGraph A B = cutWeight M.toBulkGraph f := by
    unfold throat
    rw [dif_pos hsepne]
    exact hfe
  simp only [mutualInfo, entropy] at *
  linarith
