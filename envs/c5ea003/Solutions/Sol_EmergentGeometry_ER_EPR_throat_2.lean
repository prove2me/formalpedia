-- Prove2me | solution 2 for EmergentGeometry.ER_EPR_throat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:24:14.683254+00:00
-- url     : https://prove2.me/submissions/9be1800c-7820-4548-a7fc-4197b1574a61

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V) {u v : V} (huv : u ≠ v)
    (h : 0 < mutualInfo M (single u) (single v)) :
    0 < throat M.toBulkGraph (single u) (single v) ∧
      BulkPath M.toBulkGraph u v ∧
      mutualInfo M (single u) (single v) / 2
        ≤ throat M.toBulkGraph (single u) (single v) := by
  have hiff : ∀ x y : V, x ≠ y →
      (0 < throat M.toBulkGraph (single x) (single y) ↔ BulkPath M.toBulkGraph x y) := by
    intro u v huv
    have hnn : ∀ f : Region V, 0 ≤ cutWeight M.toBulkGraph f := by
      intro f
      simp only [cutWeight]
      apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
      refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
      exact mul_nonneg (by positivity) (M.toBulkGraph.weight_nonneg a b)
    constructor
    · -- positive throat forces a bulk path
      intro hpos
      by_contra hpath
      -- the reachable set separates and has zero weight
      set R : Region V := fun x => decide (BulkPath M.toBulkGraph u x) with hR
      have hRu : R u = true := by
        rw [hR]
        simp only [decide_eq_true_eq]
        exact Relation.ReflTransGen.refl
      have hRv : R v = false := by
        rw [hR]
        simp only [decide_eq_false_iff_not]
        exact hpath
      have hreach : ∀ x : V, R x = true → BulkPath M.toBulkGraph u x := by
        intro x hx
        rw [hR] at hx
        simpa only [decide_eq_true_eq] using hx
      have hstep : ∀ x y : V, 0 < M.toBulkGraph.weight x y → R x = true → R y = true := by
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
      have hzero : cutWeight M.toBulkGraph R = 0 := by
        have hterm : ∀ a b : V, (sepBit (R a) (R b) : ℝ) * M.toBulkGraph.weight a b = 0 := by
          intro a b
          by_cases hab : R a = R b
          · simp [sepBit, hab]
          · have hw : M.toBulkGraph.weight a b = 0 := by
              by_contra hw0
              have hpos' : 0 < M.toBulkGraph.weight a b := lt_of_le_of_ne (M.toBulkGraph.weight_nonneg a b) (Ne.symm hw0)
              have hsym : 0 < M.toBulkGraph.weight b a := by rw [M.toBulkGraph.weight_symm b a]; exact hpos'
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
      have hle : throat M.toBulkGraph (single u) (single v) ≤ 0 := by
        unfold throat
        rw [dif_pos ⟨R, hmem⟩]
        calc (sepSet (single u) (single v)).inf' ⟨R, hmem⟩ (cutWeight M.toBulkGraph)
            ≤ cutWeight M.toBulkGraph R := Finset.inf'_le _ hmem
          _ = 0 := hzero
      linarith
    · -- a bulk path forces every separating surface to cut a positive edge
      intro hpath
      have hcross : ∀ f : Region V, f u = true → f v = false →
          ∃ a b : V, 0 < M.toBulkGraph.weight a b ∧ f a ≠ f b := by
        intro f hfu hfv
        have hgen : ∀ x y : V, BulkPath M.toBulkGraph x y → f x = true → f y = false →
            ∃ a b : V, 0 < M.toBulkGraph.weight a b ∧ f a ≠ f b := by
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
      have hposf : ∀ f ∈ sepSet (single u) (single v), 0 < cutWeight M.toBulkGraph f := by
        intro f hf
        simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates, single] at hf
        have hfu : f u = true := hf.1 u (by simp)
        have hfv : f v = false := hf.2 v (by simp)
        obtain ⟨a, b, hw, hne⟩ := hcross f hfu hfv
        have hterm : (0 : ℝ) < (sepBit (f a) (f b) : ℝ) * M.toBulkGraph.weight a b := by
          have : sepBit (f a) (f b) = 1 := by
            simp [sepBit, hne]
          rw [this]
          simpa using hw
        have hrow : (sepBit (f a) (f b) : ℝ) * M.toBulkGraph.weight a b
            ≤ ∑ y : V, (sepBit (f a) (f y) : ℝ) * M.toBulkGraph.weight a y :=
          Finset.single_le_sum (f := fun y => (sepBit (f a) (f y) : ℝ) * M.toBulkGraph.weight a y)
            (fun y _ => mul_nonneg (by positivity) (M.toBulkGraph.weight_nonneg a y)) (Finset.mem_univ b)
        have hall : (∑ y : V, (sepBit (f a) (f y) : ℝ) * M.toBulkGraph.weight a y)
            ≤ ∑ x : V, ∑ y : V, (sepBit (f x) (f y) : ℝ) * M.toBulkGraph.weight x y :=
          Finset.single_le_sum
            (f := fun x => ∑ y : V, (sepBit (f x) (f y) : ℝ) * M.toBulkGraph.weight x y)
            (fun x _ => Finset.sum_nonneg
              (fun y _ => mul_nonneg (by positivity) (M.toBulkGraph.weight_nonneg x y))) (Finset.mem_univ a)
        simp only [cutWeight]
        have : (0:ℝ) < ∑ x : V, ∑ y : V, (sepBit (f x) (f y) : ℝ) * M.toBulkGraph.weight x y := by
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
  have hzero : ∀ A B : Region V,
      (∀ a b, A a = true → B b = true → ¬ BulkPath M.toBulkGraph a b) →
      mutualInfo M A B = 0 := by
    intro A B h
    have hsplit : ∀ U A' B' : Region V,
        (∀ x y, U x = true → U y = false → M.weight x y = 0) →
        (∀ v, A' v = true → U v = true) → (∀ v, B' v = true → U v = false) →
        entropy M (fun v => A' v || B' v) = entropy M A' + entropy M B' := by
      intro U A B hU hA hB
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
      have hUeq : ∀ x y : V, M.toBulkGraph.weight x y ≠ 0 → U x = U y := by
        intro x y hw
        rcases Bool.eq_false_or_eq_true (U x) with hx | hx
        · rcases Bool.eq_false_or_eq_true (U y) with hy | hy
          · rw [hx, hy]
          · exact absurd (hU x y hx hy) hw
        · rcases Bool.eq_false_or_eq_true (U y) with hy | hy
          · have : M.weight y x = 0 := hU y x hy hx
            rw [M.weight_symm y x] at this
            exact absurd this hw
          · rw [hx, hy]
      -- (≤) glue the two minimal surfaces
      obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty M A) (cutWeight M.toBulkGraph)
      obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty M B) (cutWeight M.toBulkGraph)
      have hle1 : entropy M (fun v => A v || B v) ≤ entropy M A + entropy M B := by
        have hadm : (fun v => (U v && a v) || (!(U v) && b v)) ∈ admSet M (fun v => A v || B v) := by
          rw [mem_admSet]
          intro v hv
          show ((U v && a v) || (!(U v) && b v)) = (A v || B v)
          rw [(mem_admSet.mp ha) v hv, (mem_admSet.mp hb) v hv]
          rcases Bool.eq_false_or_eq_true (U v) with hUv | hUv
          · have hBv : B v = false := by
              rcases Bool.eq_false_or_eq_true (B v) with h | h
              · rw [hB v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hBv]
            simp
          · have hAv : A v = false := by
              rcases Bool.eq_false_or_eq_true (A v) with h | h
              · rw [hA v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hAv]
            simp
        have hkey := hcomb ![a, b] ![fun v => (U v && a v) || (!(U v) && b v)]
          (by
            intro u v hw
            have hUuv : U u = U v := hUeq u v hw
            simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons]
            rcases Bool.eq_false_or_eq_true (U u) with hu | hu
            · have hv : U v = true := by rw [← hUuv]; exact hu
              simp only [hu, hv, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
              omega
            · have hv : U v = false := by rw [← hUuv]; exact hu
              simp only [hu, hv, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
              omega)
        simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at hkey
        have hlow : entropy M (fun v => A v || B v)
            ≤ cutWeight M.toBulkGraph (fun v => (U v && a v) || (!(U v) && b v)) :=
          Finset.inf'_le _ hadm
        simp only [entropy] at *
        linarith
      -- (≥) split the minimal surface of the union
      obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty M (fun v => A v || B v)) (cutWeight M.toBulkGraph)
      have hle2 : entropy M A + entropy M B ≤ entropy M (fun v => A v || B v) := by
        have hadmA : (fun v => c v && U v) ∈ admSet M A := by
          rw [mem_admSet]
          intro v hv
          have hcv : c v = (A v || B v) := (mem_admSet.mp hc) v hv
          show (c v && U v) = A v
          rw [hcv]
          rcases Bool.eq_false_or_eq_true (U v) with hUv | hUv
          · have hBv : B v = false := by
              rcases Bool.eq_false_or_eq_true (B v) with h | h
              · rw [hB v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hBv]
            simp
          · have hAv : A v = false := by
              rcases Bool.eq_false_or_eq_true (A v) with h | h
              · rw [hA v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hAv]
            simp
        have hadmB : (fun v => c v && !(U v)) ∈ admSet M B := by
          rw [mem_admSet]
          intro v hv
          have hcv : c v = (A v || B v) := (mem_admSet.mp hc) v hv
          show (c v && !(U v)) = B v
          rw [hcv]
          rcases Bool.eq_false_or_eq_true (U v) with hUv | hUv
          · have hBv : B v = false := by
              rcases Bool.eq_false_or_eq_true (B v) with h | h
              · rw [hB v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hBv]
            simp
          · have hAv : A v = false := by
              rcases Bool.eq_false_or_eq_true (A v) with h | h
              · rw [hA v h] at hUv; exact absurd hUv (by simp)
              · exact h
            rw [hUv, hAv]
            simp
        have hkey := hcomb ![c] ![fun v => c v && U v, fun v => c v && !(U v)]
          (by
            intro u v hw
            have hUuv : U u = U v := hUeq u v hw
            simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons]
            rcases Bool.eq_false_or_eq_true (U u) with hu | hu
            · have hv : U v = true := by rw [← hUuv]; exact hu
              simp only [hu, hv, Bool.and_true, Bool.not_true, Bool.and_false]
              simp [sepBit]
            · have hv : U v = false := by rw [← hUuv]; exact hu
              simp only [hu, hv, Bool.and_false, Bool.not_false, Bool.and_true]
              simp [sepBit])
        simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at hkey
        have hlA : entropy M A ≤ cutWeight M.toBulkGraph (fun v => c v && U v) :=
          Finset.inf'_le _ hadmA
        have hlB : entropy M B ≤ cutWeight M.toBulkGraph (fun v => c v && !(U v)) :=
          Finset.inf'_le _ hadmB
        simp only [entropy] at *
        linarith
      linarith
    set U : Region V := fun x => decide (∃ u, A u = true ∧ BulkPath M.toBulkGraph u x) with hUdef
    have hUmem : ∀ x : V, U x = true ↔ ∃ u, A u = true ∧ BulkPath M.toBulkGraph u x := by
      intro x
      rw [hUdef]
      simp only [decide_eq_true_eq]
    have hUsplit : ∀ x y, U x = true → U y = false → M.weight x y = 0 := by
      intro x y hx hy
      by_contra hw
      have hpos : 0 < M.weight x y := lt_of_le_of_ne (M.weight_nonneg x y) (Ne.symm hw)
      obtain ⟨u, hu, hpath⟩ := (hUmem x).mp hx
      have : U y = true := (hUmem y).mpr ⟨u, hu, hpath.tail hpos⟩
      rw [hy] at this
      exact absurd this (by simp)
    have hAU : ∀ v, A v = true → U v = true := by
      intro v hv
      exact (hUmem v).mpr ⟨v, hv, Relation.ReflTransGen.refl⟩
    have hBU : ∀ v, B v = true → U v = false := by
      intro v hv
      rcases Bool.eq_false_or_eq_true (U v) with hUv | hUv
      · obtain ⟨u, hu, hpath⟩ := (hUmem v).mp hUv
        exact absurd hpath (h u v hu hv)
      · exact hUv
    have hadd := hsplit U A B hUsplit hAU hBU
    simp only [mutualInfo, hadd]
    ring
  have hle2 : ∀ A B : Region V, Disj A B →
      mutualInfo M A B ≤ 2 * throat M.toBulkGraph A B := by
    intro A B hAB
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
  have hpath : BulkPath M.toBulkGraph u v := by
    by_contra hp
    have hz : mutualInfo M (single u) (single v) = 0 := by
      refine hzero (single u) (single v) (fun a b ha hb => ?_)
      have hau : a = u := by simpa [single] using ha
      have hbv : b = v := by simpa [single] using hb
      subst hau
      subst hbv
      exact hp
    rw [hz] at h
    exact absurd h (by norm_num)
  have hdisj : Disj (single u) (single v) := by
    intro x hx
    have hxu : x = u := by simpa [single] using hx
    simp only [single, decide_eq_false_iff_not, hxu]
    exact huv
  have hb := hle2 (single u) (single v) hdisj
  exact ⟨(hiff u v huv).mpr hpath, hpath, by linarith⟩
