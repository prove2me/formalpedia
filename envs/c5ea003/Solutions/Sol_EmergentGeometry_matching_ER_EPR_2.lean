-- Prove2me | solution 2 for EmergentGeometry.matching_ER_EPR
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:16:26.282275+00:00
-- url     : https://prove2.me/submissions/39cd0f44-3ff1-45df-b005-6214fe15a573

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRQuantumBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset Classical in
theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (i j : Fin n) (b c : Bool) :
    (i = j ∧ b ≠ c ∧ 0 < w i →
        BulkPath (matchingModel w hw).toBulkGraph (i, b) (j, c) ∧
        0 < mutualInfo (matchingModel w hw) (single (i, b)) (single (j, c)))
      ∧ (i ≠ j →
        ¬ BulkPath (matchingModel w hw).toBulkGraph (i, b) (j, c) ∧
        mutualInfo (matchingModel w hw) (single (i, b)) (single (j, c)) = 0) := by
  -- (0) no bridge between two regions forces zero mutual information (abstract model)
  have hzero : ∀ (MM : HoloModel (Fin n × Bool)) (A B : Region (Fin n × Bool)),
      (∀ a b, A a = true → B b = true → ¬ BulkPath MM.toBulkGraph a b) →
      mutualInfo MM A B = 0 := by
    intro MM A B h
    have hsplit : ∀ U A' B' : Region (Fin n × Bool),
        (∀ x y, U x = true → U y = false → MM.weight x y = 0) →
        (∀ v, A' v = true → U v = true) → (∀ v, B' v = true → U v = false) →
        entropy MM (fun v => A' v || B' v) = entropy MM A' + entropy MM B' := by
      intro U A B hU hA hB
      have hcomb : ∀ {m' n' : ℕ} (F : Fin m' → Region (Fin n × Bool)) (H : Fin n' → Region (Fin n × Bool)),
          (∀ u v : (Fin n × Bool), MM.toBulkGraph.weight u v ≠ 0 →
            ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) →
          ∑ i, cutWeight MM.toBulkGraph (H i) ≤ ∑ j, cutWeight MM.toBulkGraph (F j) := by
        intro m' n' F H h
        -- pointwise comparison of the weighted separation counts
        have hpt : ∀ u v : (Fin n × Bool),
            ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v
              ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v := by
          intro u v
          by_cases hw : MM.toBulkGraph.weight u v = 0
          · simp [hw]
          · have hle : ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ)
                ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) := by
              exact_mod_cast h u v hw
            exact mul_le_mul_of_nonneg_right hle (MM.toBulkGraph.weight_nonneg u v)
        -- collect each family into a single double sum
        have hcollect : ∀ {k : ℕ} (K : Fin k → Region (Fin n × Bool)),
            (∑ i, cutWeight MM.toBulkGraph (K i))
              = (∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v) / 2 := by
          intro k K
          simp only [cutWeight]
          rw [← Finset.sum_div]
          congr 1
          calc (∑ i, ∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), (sepBit (K i u) (K i v) : ℝ) * MM.toBulkGraph.weight u v)
              = ∑ u : (Fin n × Bool), ∑ i, ∑ v : (Fin n × Bool), (sepBit (K i u) (K i v) : ℝ) * MM.toBulkGraph.weight u v :=
                Finset.sum_comm
            _ = ∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), ∑ i, (sepBit (K i u) (K i v) : ℝ) * MM.toBulkGraph.weight u v :=
                Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
            _ = ∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v := by
                refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
                push_cast
                rw [Finset.sum_mul]
        rw [hcollect H, hcollect F]
        have hsum : (∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v)
            ≤ ∑ u : (Fin n × Bool), ∑ v : (Fin n × Bool), ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * MM.toBulkGraph.weight u v :=
          Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
        linarith
      have hUeq : ∀ x y : (Fin n × Bool), MM.toBulkGraph.weight x y ≠ 0 → U x = U y := by
        intro x y hw
        rcases Bool.eq_false_or_eq_true (U x) with hx | hx
        · rcases Bool.eq_false_or_eq_true (U y) with hy | hy
          · rw [hx, hy]
          · exact absurd (hU x y hx hy) hw
        · rcases Bool.eq_false_or_eq_true (U y) with hy | hy
          · have : MM.weight y x = 0 := hU y x hy hx
            rw [MM.weight_symm y x] at this
            exact absurd this hw
          · rw [hx, hy]
      -- (≤) glue the two minimal surfaces
      obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty MM A) (cutWeight MM.toBulkGraph)
      obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty MM B) (cutWeight MM.toBulkGraph)
      have hle1 : entropy MM (fun v => A v || B v) ≤ entropy MM A + entropy MM B := by
        have hadm : (fun v => (U v && a v) || (!(U v) && b v)) ∈ admSet MM (fun v => A v || B v) := by
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
        have hlow : entropy MM (fun v => A v || B v)
            ≤ cutWeight MM.toBulkGraph (fun v => (U v && a v) || (!(U v) && b v)) :=
          Finset.inf'_le _ hadm
        simp only [entropy] at *
        linarith
      -- (≥) split the minimal surface of the union
      obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_inf'
        (admSet_nonempty MM (fun v => A v || B v)) (cutWeight MM.toBulkGraph)
      have hle2 : entropy MM A + entropy MM B ≤ entropy MM (fun v => A v || B v) := by
        have hadmA : (fun v => c v && U v) ∈ admSet MM A := by
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
        have hadmB : (fun v => c v && !(U v)) ∈ admSet MM B := by
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
        have hlA : entropy MM A ≤ cutWeight MM.toBulkGraph (fun v => c v && U v) :=
          Finset.inf'_le _ hadmA
        have hlB : entropy MM B ≤ cutWeight MM.toBulkGraph (fun v => c v && !(U v)) :=
          Finset.inf'_le _ hadmB
        simp only [entropy] at *
        linarith
      linarith
    set U : Region (Fin n × Bool) := fun x => decide (∃ u, A u = true ∧ BulkPath MM.toBulkGraph u x) with hUdef
    have hUmem : ∀ x : (Fin n × Bool), U x = true ↔ ∃ u, A u = true ∧ BulkPath MM.toBulkGraph u x := by
      intro x
      rw [hUdef]
      simp only [decide_eq_true_eq]
    have hUsplit : ∀ x y, U x = true → U y = false → MM.weight x y = 0 := by
      intro x y hx hy
      by_contra hw
      have hpos : 0 < MM.weight x y := lt_of_le_of_ne (MM.weight_nonneg x y) (Ne.symm hw)
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
  -- (1) the cut weight of any region, collapsed onto the matched pairs
  have hcw : ∀ f : Region (Fin n × Bool),
      cutWeight (matchingModel w hw).toBulkGraph f
        = (∑ k : Fin n, ∑ d : Bool, (sepBit (f (k, d)) (f (k, !d)) : ℝ) * w k) / 2 := by
    intro f
    have hwt : ∀ p q : Fin n × Bool,
        (matchingModel w hw).toBulkGraph.weight p q
          = if p.1 = q.1 ∧ p.2 ≠ q.2 then w p.1 else 0 := fun p q => rfl
    simp only [cutWeight]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [Fintype.sum_prod_type]
    have hinner : ∀ k' : Fin n,
        (∑ d' : Bool, (sepBit (f (k, d)) (f (k', d')) : ℝ)
            * (matchingModel w hw).toBulkGraph.weight (k, d) (k', d'))
          = if k' = k then (sepBit (f (k, d)) (f (k, !d)) : ℝ) * w k else 0 := by
      intro k'
      by_cases hk : k' = k
      · subst hk
        rw [if_pos rfl, Fintype.sum_bool]
        cases d <;> simp [hwt]
      · rw [if_neg hk]
        refine Finset.sum_eq_zero (fun d' _ => ?_)
        rw [hwt]
        simp only [Ne.symm hk, false_and, if_false, mul_zero]
    rw [Finset.sum_congr rfl (fun k' _ => hinner k')]
    rw [Finset.sum_ite_eq' Finset.univ k (fun _ => (sepBit (f (k, d)) (f (k, !d)) : ℝ) * w k)]
    simp
  -- (2) no interior cells: each region is its own minimal surface
  have hent : ∀ A : Region (Fin n × Bool),
      entropy (matchingModel w hw) A = cutWeight (matchingModel w hw).toBulkGraph A := by
    intro A
    apply le_antisymm
    · exact Finset.inf'_le _ (mem_admSet.mpr (fun v _ => rfl))
    · refine Finset.le_inf' _ _ (fun g hg => ?_)
      have hga : g = A := by
        funext v
        exact (mem_admSet.mp hg) v rfl
      rw [hga]
  -- (3) one cell of a matched pair has cut weight exactly its own edge
  have hsingle : ∀ (k : Fin n) (d : Bool),
      cutWeight (matchingModel w hw).toBulkGraph (single (k, d)) = w k := by
    intro k d
    rw [hcw]
    have hrow : ∀ k' : Fin n,
        (∑ d' : Bool, (sepBit (single (k, d) (k', d')) (single (k, d) (k', !d')) : ℝ) * w k')
          = if k' = k then 2 * w k else 0 := by
      intro k'
      by_cases hk : k' = k
      · subst hk
        rw [if_pos rfl, Fintype.sum_bool]
        cases d <;> simp [single, sepBit] <;> ring
      · rw [if_neg hk]
        refine Finset.sum_eq_zero (fun d' _ => ?_)
        have h1 : single (k, d) (k', d') = false := by
          simp [single, Prod.ext_iff, hk]
        have h2 : single (k, d) (k', !d') = false := by
          simp [single, Prod.ext_iff, hk]
        rw [h1, h2]
        simp [sepBit]
    rw [Finset.sum_congr rfl (fun k' _ => hrow k')]
    rw [Finset.sum_ite_eq' Finset.univ k (fun _ => 2 * w k)]
    simp
  -- (4) reachability cannot leave a matched pair
  have hidx : ∀ p q : Fin n × Bool,
      BulkPath (matchingModel w hw).toBulkGraph p q → p.1 = q.1 := by
    intro p q hpq
    induction hpq with
    | refl => rfl
    | @tail x y hxy hstep ih =>
        refine ih.trans ?_
        by_contra hne
        have hz : (matchingModel w hw).toBulkGraph.weight x y = 0 := by
          show (if x.1 = y.1 ∧ x.2 ≠ y.2 then w x.1 else 0) = 0
          rw [if_neg (fun hh => hne hh.1)]
        have hpos : (0 : ℝ) < (matchingModel w hw).toBulkGraph.weight x y := hstep
        rw [hz] at hpos
        exact absurd hpos (by simp)
  constructor
  · rintro ⟨rfl, hbc, hwi⟩
    have hcb : c = !b := by
      cases b <;> cases c <;> first | rfl | exact absurd rfl hbc
    subst hcb
    refine ⟨Relation.ReflTransGen.single ?_, ?_⟩
    · show (0 : ℝ) < (matchingModel w hw).toBulkGraph.weight (i, b) (i, !b)
      show (0 : ℝ) < (if (i, b).1 = (i, !b).1 ∧ (i, b).2 ≠ (i, !b).2 then w (i, b).1 else 0)
      rw [if_pos ⟨rfl, by cases b <;> simp⟩]
      exact hwi
    · have hunion : cutWeight (matchingModel w hw).toBulkGraph
          (fun v => single (i, b) v || single (i, !b) v) = 0 := by
        rw [hcw]
        have hrow : ∀ k' : Fin n,
            (∑ d' : Bool, (sepBit ((fun v => single (i, b) v || single (i, !b) v) (k', d'))
                ((fun v => single (i, b) v || single (i, !b) v) (k', !d')) : ℝ) * w k') = 0 := by
          intro k'
          refine Finset.sum_eq_zero (fun d' _ => ?_)
          by_cases hk : k' = i
          · subst hk
            have e1 : ((fun v => single (k', b) v || single (k', !b) v) (k', d')) = true := by
              cases b <;> cases d' <;> simp [single]
            have e2 : ((fun v => single (k', b) v || single (k', !b) v) (k', !d')) = true := by
              cases b <;> cases d' <;> simp [single]
            rw [e1, e2]
            simp [sepBit]
          · have e1 : ((fun v => single (i, b) v || single (i, !b) v) (k', d')) = false := by
              simp [single, Prod.ext_iff, hk]
            have e2 : ((fun v => single (i, b) v || single (i, !b) v) (k', !d')) = false := by
              simp [single, Prod.ext_iff, hk]
            rw [e1, e2]
            simp [sepBit]
        rw [Finset.sum_congr rfl (fun k' _ => hrow k')]
        simp
      have h1 := hent (single (i, b))
      have h2 := hent (single (i, !b))
      have h3 := hent (fun v => single (i, b) v || single (i, !b) v)
      have s1 := hsingle i b
      have s2 := hsingle i (!b)
      simp only [mutualInfo, h1, h2, h3, s1, s2, hunion]
      linarith
  · intro hij
    have hnp : ¬ BulkPath (matchingModel w hw).toBulkGraph (i, b) (j, c) := by
      intro hp
      exact hij (hidx _ _ hp)
    refine ⟨hnp, hzero (matchingModel w hw) (single (i, b)) (single (j, c))
      (fun a b' ha hb' => ?_)⟩
    have hai : a = (i, b) := by simpa [single] using ha
    have hbj : b' = (j, c) := by simpa [single] using hb'
    subst hai
    subst hbj
    exact hnp
