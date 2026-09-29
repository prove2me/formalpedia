-- Prove2me | solution 2 for EmergentGeometry.throat_pos_iff_bulkPath
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:46:41.110208+00:00
-- url     : https://prove2.me/submissions/3aed1101-213d-4a20-aa4e-6c02306a75c2

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : BulkGraph V) {u v : V} (huv : u ≠ v) :
    0 < throat G (single u) (single v) ↔ BulkPath G u v := by
  have hnn : ∀ f : Region V, 0 ≤ cutWeight G f := by
    intro f
    simp only [cutWeight]
    apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
    refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
    exact mul_nonneg (by positivity) (G.weight_nonneg a b)
  constructor
  · -- positive throat forces a bulk path
    intro hpos
    by_contra hpath
    -- the reachable set separates and has zero weight
    set R : Region V := fun x => decide (BulkPath G u x) with hR
    have hRu : R u = true := by
      rw [hR]
      simp only [decide_eq_true_eq]
      exact Relation.ReflTransGen.refl
    have hRv : R v = false := by
      rw [hR]
      simp only [decide_eq_false_iff_not]
      exact hpath
    have hreach : ∀ x : V, R x = true → BulkPath G u x := by
      intro x hx
      rw [hR] at hx
      simpa only [decide_eq_true_eq] using hx
    have hstep : ∀ x y : V, 0 < G.weight x y → R x = true → R y = true := by
      intro x y hxy hx
      rw [hR]
      simp only [decide_eq_true_eq]
      exact (hreach x hx).tail hxy
    have hmem : R ∈ sepSet (single u) (single v) := by
      simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates, single]
      constructor
      · intro x hx
        have hxu : x = u := by simpa using hx
        subst hxu
        exact hRu
      · intro x hx
        have hxv : x = v := by simpa using hx
        subst hxv
        exact hRv
    have hzero : cutWeight G R = 0 := by
      have hterm : ∀ a b : V, (sepBit (R a) (R b) : ℝ) * G.weight a b = 0 := by
        intro a b
        by_cases hab : R a = R b
        · simp [sepBit, hab]
        · have hw : G.weight a b = 0 := by
            by_contra hw0
            have hpos' : 0 < G.weight a b := lt_of_le_of_ne (G.weight_nonneg a b) (Ne.symm hw0)
            have hsym : 0 < G.weight b a := by rw [G.weight_symm b a]; exact hpos'
            rcases Bool.eq_false_or_eq_true (R a) with ha | ha
            · have hb : R b = true := hstep a b hpos' ha
              exact hab (by rw [ha, hb])
            · rcases Bool.eq_false_or_eq_true (R b) with hb | hb
              · have hcon : R a = true := hstep b a hsym hb
                rw [ha] at hcon
                exact absurd hcon (by simp)
              · exact hab (by rw [ha, hb])
          simp [hw]
      simp only [cutWeight]
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
      simp
    have hle : throat G (single u) (single v) ≤ 0 := by
      unfold throat
      rw [dif_pos ⟨R, hmem⟩]
      calc (sepSet (single u) (single v)).inf' ⟨R, hmem⟩ (cutWeight G)
          ≤ cutWeight G R := Finset.inf'_le _ hmem
        _ = 0 := hzero
    linarith
  · -- a bulk path forces every separating surface to cut a positive edge
    intro hpath
    have hcross : ∀ f : Region V, f u = true → f v = false →
        ∃ a b : V, 0 < G.weight a b ∧ f a ≠ f b := by
      intro f hfu hfv
      have hgen : ∀ x y : V, BulkPath G x y → f x = true → f y = false →
          ∃ a b : V, 0 < G.weight a b ∧ f a ≠ f b := by
        intro x y hxy
        induction hxy with
        | refl =>
            intro h1 h2
            exact absurd (h1.symm.trans h2) (by simp)
        | @tail z w hxz hzw ih =>
            intro h1 h2
            by_cases hz : f z = true
            · refine ⟨z, w, hzw, ?_⟩
              rw [hz, h2]
              simp
            · rw [Bool.not_eq_true] at hz
              exact ih h1 hz
      exact hgen u v hpath hfu hfv
    have hposf : ∀ f ∈ sepSet (single u) (single v), 0 < cutWeight G f := by
      intro f hf
      simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates, single] at hf
      have hfu : f u = true := hf.1 u (by simp)
      have hfv : f v = false := hf.2 v (by simp)
      obtain ⟨a, b, hw, hne⟩ := hcross f hfu hfv
      have hterm : (0 : ℝ) < (sepBit (f a) (f b) : ℝ) * G.weight a b := by
        have : sepBit (f a) (f b) = 1 := by
          simp [sepBit, hne]
        rw [this]
        simpa using hw
      have hrow : (sepBit (f a) (f b) : ℝ) * G.weight a b
          ≤ ∑ y : V, (sepBit (f a) (f y) : ℝ) * G.weight a y :=
        Finset.single_le_sum (f := fun y => (sepBit (f a) (f y) : ℝ) * G.weight a y)
          (fun y _ => mul_nonneg (by positivity) (G.weight_nonneg a y)) (Finset.mem_univ b)
      have hall : (∑ y : V, (sepBit (f a) (f y) : ℝ) * G.weight a y)
          ≤ ∑ x : V, ∑ y : V, (sepBit (f x) (f y) : ℝ) * G.weight x y :=
        Finset.single_le_sum
          (f := fun x => ∑ y : V, (sepBit (f x) (f y) : ℝ) * G.weight x y)
          (fun x _ => Finset.sum_nonneg
            (fun y _ => mul_nonneg (by positivity) (G.weight_nonneg x y))) (Finset.mem_univ a)
      simp only [cutWeight]
      have : (0:ℝ) < ∑ x : V, ∑ y : V, (sepBit (f x) (f y) : ℝ) * G.weight x y := by
        linarith
      linarith
    have hne : (sepSet (single u) (single v)).Nonempty := by
      refine ⟨single u, ?_⟩
      simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates, single]
      refine ⟨fun x hx => hx, fun x hx => ?_⟩
      have : x = v := by simpa using hx
      subst this
      simpa using (Ne.symm huv)
    unfold throat
    rw [dif_pos hne]
    exact (Finset.lt_inf'_iff hne).mpr hposf
