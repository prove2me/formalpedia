-- Prove2me | solution 1 for EmergentGeometry.pairModel_maxflow_eq_throat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T23:56:40.870568+00:00
-- url     : https://prove2.me/submissions/3780239f-8c75-49e9-82a5-ed85e62eb8f2

import Mathlib
import Definitions.Def_Novelty_EREPRBitThreads
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

set_option maxHeartbeats 1600000 in
open Finset EmergentGeometry in
theorem solution (w : ℝ) (hw : 0 ≤ w) :
    (pairThreads w hw).Conserved (single 0) (single 1) ∧
      (pairThreads w hw).value (single 0)
        = throat (pairModel w hw).toBulkGraph (single 0) (single 1) ∧
      (∀ T : BitThreads (pairModel w hw).toBulkGraph,
        T.Conserved (single 0) (single 1) →
          T.value (single 0) ≤ (pairThreads w hw).value (single 0)) ∧
      (pairThreads w hw).value (single 0)
        = mutualInfo (pairModel w hw) (single 0) (single 1) / 2 := by
  classical
  -- ==== EmergentGeometry lemmas, proved from the definitions ====
  have hsym : ∀ a b : Bool, sepBit a b = sepBit b a := by
    intro a b; cases a <;> cases b <;> simp [sepBit]
  -- the cut weight of the two-cell wormhole
  have hcut : ∀ (w : ℝ) (hw : 0 ≤ w) (f : Region (Fin 2)),
      cutWeight (pairModel w hw).toBulkGraph f = (sepBit (f 0) (f 1) : ℝ) * w := by
    intro w hw f
    simp only [cutWeight, pairModel]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    have e00 : sepBit (f 0) (f 0) = 0 := by simp [sepBit]
    have e11 : sepBit (f 1) (f 1) = 0 := by simp [sepBit]
    have e10 : sepBit (f 1) (f 0) = sepBit (f 0) (f 1) := hsym _ _
    simp only [e00, e11, e10]
    norm_num
  -- with no bulk cells the only admissible region is `A` itself
  have hadm : ∀ (w : ℝ) (hw : 0 ≤ w) (A : Region (Fin 2)),
      admSet (pairModel w hw) A = {A} := by
    intro w hw A
    ext f
    simp only [admSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Admissible, pairModel]
    exact ⟨fun h => funext fun v => h v trivial, fun h v _ => by rw [h]⟩
  have hent : ∀ (w : ℝ) (hw : 0 ≤ w) (A : Region (Fin 2)),
      entropy (pairModel w hw) A = (sepBit (A 0) (A 1) : ℝ) * w := by
    intro w hw A
    rw [← hcut w hw A]
    have hgen : ∀ (s : Finset (Region (Fin 2))) (h : s.Nonempty), s = {A} →
        s.inf' h (cutWeight (pairModel w hw).toBulkGraph)
          = cutWeight (pairModel w hw).toBulkGraph A := by
      intro s h hs
      subst hs
      simp
    exact hgen _ _ (hadm w hw A)
  have hsepSet : sepSet (single (0 : Fin 2)) (single (1 : Fin 2)) = {single (0 : Fin 2)} := by
    ext f
    simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Separates, single]
    constructor
    · rintro ⟨h1, h2⟩
      funext v
      fin_cases v
      · simpa using h1 0 (by simp)
      · simpa using h2 1 (by simp)
    · intro h
      subst h
      refine ⟨fun v hv => hv, ?_⟩
      decide
  have hthroat : ∀ (w : ℝ) (hw : 0 ≤ w),
      throat (pairModel w hw).toBulkGraph (single 0) (single 1) = w := by
    intro w hw
    have hne : (sepSet (single (0 : Fin 2)) (single (1 : Fin 2))).Nonempty := by
      rw [hsepSet]; exact ⟨_, Finset.mem_singleton_self _⟩
    rw [throat, dif_pos hne]
    have hgen : ∀ (s : Finset (Region (Fin 2))) (h : s.Nonempty),
        s = {single (0 : Fin 2)} →
        s.inf' h (cutWeight (pairModel w hw).toBulkGraph)
          = cutWeight (pairModel w hw).toBulkGraph (single 0) := by
      intro s h hs; subst hs; simp
    rw [hgen _ _ hsepSet, hcut]
    norm_num [single, sepBit]
  have hmi : ∀ (w : ℝ) (hw : 0 ≤ w),
      mutualInfo (pairModel w hw) (single 0) (single 1) = 2 * w := by
    intro w hw
    rw [mutualInfo, hent, hent, hent]
    norm_num [single, sepBit]
    ring
  have hcutcross : ∀ (G : BulkGraph (Fin 2)) (σ : Region (Fin 2)),
      cutWeight G σ = ∑ x ∈ univ.filter (fun v => σ v = true),
        ∑ y ∈ univ.filter (fun v => ¬ (σ v = true)), G.weight x y := by
    intro G σ
    classical
    rw [cutWeight]
    have hsplit : ∀ g : Fin 2 → ℝ, ∑ v, g v
        = ∑ v ∈ univ.filter (fun v => σ v = true), g v
          + ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)), g v := fun g =>
      (Finset.sum_filter_add_sum_filter_not univ (fun v => σ v = true) g).symm
    rw [hsplit (fun x => ∑ v, (sepBit (σ x) (σ v) : ℝ) * G.weight x v)]
    have hSS : ∀ x ∈ univ.filter (fun v => σ v = true),
        ∑ v ∈ univ.filter (fun v => σ v = true),
          (sepBit (σ x) (σ v) : ℝ) * G.weight x v = 0 := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine Finset.sum_eq_zero fun v hv => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [sepBit, hx, hv]
    have hCC : ∀ x ∈ univ.filter (fun v => ¬ (σ v = true)),
        ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)),
          (sepBit (σ x) (σ v) : ℝ) * G.weight x v = 0 := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hx
      refine Finset.sum_eq_zero fun v hv => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hv
      simp [sepBit, hx, hv]
    have hSC : ∀ x ∈ univ.filter (fun v => σ v = true),
        ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)),
          (sepBit (σ x) (σ v) : ℝ) * G.weight x v
        = ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)), G.weight x v := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine Finset.sum_congr rfl fun v hv => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hv
      simp [sepBit, hx, hv]
    have hCS : ∀ x ∈ univ.filter (fun v => ¬ (σ v = true)),
        ∑ v ∈ univ.filter (fun v => σ v = true),
          (sepBit (σ x) (σ v) : ℝ) * G.weight x v
        = ∑ v ∈ univ.filter (fun v => σ v = true), G.weight x v := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hx
      refine Finset.sum_congr rfl fun v hv => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [sepBit, hx, hv]
    have hswap : ∑ x ∈ univ.filter (fun v => ¬ (σ v = true)),
        ∑ v ∈ univ.filter (fun v => σ v = true), G.weight x v
        = ∑ x ∈ univ.filter (fun v => σ v = true),
          ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)), G.weight x v := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun v _ => G.weight_symm v x
    have hA : ∑ x ∈ univ.filter (fun v => σ v = true),
          (∑ v, (sepBit (σ x) (σ v) : ℝ) * G.weight x v)
        = ∑ x ∈ univ.filter (fun v => σ v = true),
          ∑ v ∈ univ.filter (fun v => ¬ (σ v = true)), G.weight x v := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hsplit (fun v => (sepBit (σ x) (σ v) : ℝ) * G.weight x v), hSS x hx, hSC x hx, zero_add]
    have hB : ∑ x ∈ univ.filter (fun v => ¬ (σ v = true)),
          (∑ v, (sepBit (σ x) (σ v) : ℝ) * G.weight x v)
        = ∑ x ∈ univ.filter (fun v => ¬ (σ v = true)),
          ∑ v ∈ univ.filter (fun v => σ v = true), G.weight x v := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hsplit (fun v => (sepBit (σ x) (σ v) : ℝ) * G.weight x v), hCC x hx, hCS x hx, add_zero]
    rw [hA, hB, hswap]
    ring
  have value_le_cutWeight : ∀ {G : BulkGraph (Fin 2)} (T : BitThreads G)
      {A B σ : Region (Fin 2)}, T.Conserved A B → Separates A B σ →
      T.value A ≤ cutWeight G σ := by
    intro G T A B σ hcons hsep
    have hcw := hcutcross G σ
    classical
    set S : Finset (Fin 2) := univ.filter (fun v => σ v = true) with hSdef
    set C : Finset (Fin 2) := univ.filter (fun v => ¬ (σ v = true)) with hCdef
    have hsplit : ∀ g : Fin 2 → ℝ, ∑ v, g v = ∑ v ∈ S, g v + ∑ v ∈ C, g v := fun g =>
      (Finset.sum_filter_add_sum_filter_not univ (fun v => σ v = true) g).symm
    -- conservation moves the source sum onto the whole of `σ`
    have hval : T.value A = ∑ x ∈ S, T.div x := by
      rw [BitThreads.value]
      refine Finset.sum_subset ?_ ?_
      · intro x hx
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hsep.1 x hx
      · intro x hxS hxA
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxA
        have hA : A x = false := by
          cases hax : A x with
          | false => rfl
          | true => exact absurd hax hxA
        have hB : B x = false := by
          cases hbx : B x with
          | false => rfl
          | true =>
              have := hsep.2 x hbx
              rw [this] at hxS
              exact absurd hxS (by simp)
        exact hcons x hA hB
    -- the internal flux cancels by antisymmetry
    have hzero : ∑ x ∈ S, ∑ y ∈ S, T.flow x y = 0 := by
      have h1 : ∑ x ∈ S, ∑ y ∈ S, T.flow x y
          = ∑ x ∈ S, ∑ y ∈ S, (-(T.flow y x)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => T.antisymm x y
      have h2 : ∑ x ∈ S, ∑ y ∈ S, (-(T.flow y x))
          = -(∑ x ∈ S, ∑ y ∈ S, T.flow y x) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_neg_distrib _
      have h3 : ∑ x ∈ S, ∑ y ∈ S, T.flow y x = ∑ x ∈ S, ∑ y ∈ S, T.flow x y :=
        Finset.sum_comm
      linarith [h1, h2, h3]
    have hstep : ∑ x ∈ S, T.div x = ∑ x ∈ S, ∑ y ∈ C, T.flow x y := by
      have := Finset.sum_congr rfl (fun x (_ : x ∈ S) => hsplit (fun y => T.flow x y))
      simp only [BitThreads.div]
      rw [this, Finset.sum_add_distrib, hzero, zero_add]
    have hcap : ∑ x ∈ S, ∑ y ∈ C, T.flow x y ≤ ∑ x ∈ S, ∑ y ∈ C, G.weight x y :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => T.capacity x y
    rw [hval, hstep, hcw]
    exact hcap
  have exists_min_throat_surface : ∀ (G : BulkGraph (Fin 2)) {A B : Region (Fin 2)}, Disj A B →
      ∃ f, Separates A B f ∧ throat G A B = cutWeight G f := by
    intro G A B h
    have hA : Separates A B A := by
      refine ⟨fun v hv => hv, fun v hv => ?_⟩
      cases hav : A v with
      | false => rfl
      | true =>
          have hB := h v hav
          rw [hB] at hv
          exact absurd hv (by simp)
    have hne : (sepSet A B).Nonempty := ⟨A, by simp [sepSet, hA]⟩
    rw [throat, dif_pos hne]
    obtain ⟨f, hf, hfeq⟩ := Finset.exists_mem_eq_inf' hne (cutWeight G)
    refine ⟨f, ?_, hfeq⟩
    simpa [sepSet] using hf
  have pairModel_throat : ∀ (w : ℝ) (hw : 0 ≤ w),
      throat (pairModel w hw).toBulkGraph (single 0) (single 1) = w ∧
        mutualInfo (pairModel w hw) (single 0) (single 1)
          = 2 * throat (pairModel w hw).toBulkGraph (single 0) (single 1) := by
    intro w hw
    refine ⟨hthroat w hw, ?_⟩
    rw [hthroat w hw, hmi w hw]
  have pairModel_mutualInfo : ∀ (w : ℝ) (hw : 0 ≤ w),
      mutualInfo (pairModel w hw) (single 0) (single 1) = 2 * w := hmi
  -- ==== end of inlined lemmas ====
  classical
  have hthroat : throat (pairModel w hw).toBulkGraph (single 0) (single 1) = w :=
    (pairModel_throat w hw).1
  -- conservation is vacuous: each of the two cells lies in one of the two regions
  have hcons : (pairThreads w hw).Conserved (single 0) (single 1) := by
    intro v h0 h1
    fin_cases v <;> simp [single] at h0 h1
  -- the configuration carries exactly `w` out of cell `0`
  have hval : (pairThreads w hw).value (single 0) = w := by
    rw [BitThreads.value]
    have hfil : (univ.filter (fun x : Fin 2 => single (0 : Fin 2) x = true)) = {0} := by
      ext x
      fin_cases x <;> simp [single]
    rw [hfil, Finset.sum_singleton, BitThreads.div]
    simp [pairThreads, Fin.sum_univ_two]
  have hdisj : Disj (single (0 : Fin 2)) (single (1 : Fin 2)) := by
    intro v hv
    fin_cases v <;> simp [single] at hv ⊢
  refine ⟨hcons, ?_, ?_, ?_⟩
  · rw [hval, hthroat]
  · intro T hT
    obtain ⟨f, hsep, hcut⟩ :=
      exists_min_throat_surface (pairModel w hw).toBulkGraph hdisj
    rw [hval]
    calc T.value (single 0)
        ≤ cutWeight (pairModel w hw).toBulkGraph f :=
          value_le_cutWeight T hT hsep
      _ = throat (pairModel w hw).toBulkGraph (single 0) (single 1) := hcut.symm
      _ = w := hthroat
  · rw [hval, pairModel_mutualInfo w hw]
    ring
