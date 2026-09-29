-- Prove2me | solution 2 for MarkovMixing.transport_metric
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:59:28.644656+00:00
-- url     : https://prove2.me/submissions/64f98344-ba8d-444a-98f0-c94663453dc6

import Definitions.Def_mm_transport
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace Transport

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cost_nonneg {ρ : V → V → ℝ} (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    {q : V × V → ℝ} (hq : ∀ p, 0 ≤ q p) : 0 ≤ ∑ p : V × V, ρ p.1 p.2 * q p :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hρ0 _ _) (hq p)

lemma bddBelow_costs {ρ : V → V → ℝ} (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (μ ν : V → ℝ) :
    BddBelow {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      e = ∑ p : V × V, ρ p.1 p.2 * q p} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, hq, rfl⟩
  exact cost_nonneg hρ0 hq.1.1

/-- The product coupling. -/
lemma product_isCoupling {μ ν : V → ℝ} (hμ : IsDist μ) (hν : IsDist ν) :
    IsCoupling μ ν (fun p : V × V => μ p.1 * ν p.2) := by
  refine ⟨⟨fun p => mul_nonneg (hμ.1 _) (hν.1 _), ?_⟩, ?_, ?_⟩
  · show ∑ p : V × V, μ p.1 * ν p.2 = 1
    rw [Fintype.sum_prod_type]
    have e : ∀ x : V, ∑ y, μ x * ν y = μ x := by
      intro x; rw [← Finset.mul_sum, hν.2, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => e x), hμ.2]
  · intro x
    show ∑ y, μ x * ν y = μ x
    rw [← Finset.mul_sum, hν.2, mul_one]
  · intro y
    show ∑ x, μ x * ν y = ν y
    have e : ∀ x : V, μ x * ν y = ν y * μ x := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hμ.2, mul_one]

/-- The infimum defining the transportation distance is attained. -/
lemma exists_optimal {ρ : V → V → ℝ} (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    {μ ν : V → ℝ} (hμ : IsDist μ) (hν : IsDist ν) :
    ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      transportDist ρ μ ν = ∑ p : V × V, ρ p.1 p.2 * q p := by
  classical
  set C : Set (V × V → ℝ) := {q | IsCoupling μ ν q} with hC_def
  have hCne : C.Nonempty := ⟨_, product_isCoupling hμ hν⟩
  have hbox : C ⊆ Set.pi Set.univ (fun _ : V × V => Set.Icc (0 : ℝ) 1) := by
    intro q hq p _
    refine ⟨hq.1.1 p, ?_⟩
    have h1 : q p ≤ ∑ p' : V × V, q p' :=
      Finset.single_le_sum (f := q) (fun i _ => hq.1.1 i) (Finset.mem_univ p)
    rw [hq.1.2] at h1
    exact h1
  have hclosed : IsClosed C := by
    have e : C = ((⋂ p : V × V, {q : V × V → ℝ | 0 ≤ q p})
        ∩ {q : V × V → ℝ | ∑ p : V × V, q p = 1}
        ∩ (⋂ x : V, {q : V × V → ℝ | ∑ y, q (x, y) = μ x}))
        ∩ (⋂ y : V, {q : V × V → ℝ | ∑ x, q (x, y) = ν y}) := by
      ext q
      simp only [hC_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        MarkovMixing.IsCoupling, MarkovMixing.IsDist]
      tauto
    rw [e]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
    · exact isClosed_eq (continuous_finset_sum _ fun p _ => continuous_apply p) continuous_const
    · exact isClosed_iInter fun x =>
        isClosed_eq (continuous_finset_sum _ fun y _ => continuous_apply (x, y)) continuous_const
    · exact isClosed_iInter fun y =>
        isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply (x, y)) continuous_const
  have hcompact : IsCompact C :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hclosed hbox
  have hcont : Continuous (fun q : V × V → ℝ => ∑ p : V × V, ρ p.1 p.2 * q p) :=
    continuous_finset_sum _ fun p _ => (continuous_apply p).const_mul _
  obtain ⟨q0, hq0mem, hq0min⟩ := hcompact.exists_isMinOn hCne hcont.continuousOn
  refine ⟨q0, hq0mem, ?_⟩
  have hmem : (∑ p : V × V, ρ p.1 p.2 * q0 p) ∈
      {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧ e = ∑ p : V × V, ρ p.1 p.2 * q p} :=
    ⟨q0, hq0mem, rfl⟩
  refine le_antisymm (csInf_le (bddBelow_costs hρ0 μ ν) hmem) ?_
  refine le_csInf ⟨_, hmem⟩ ?_
  rintro e ⟨q, hq, rfl⟩
  exact hq0min hq

end Transport

open Transport

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y)
    (hρsymm : ∀ x y : V, ρ x y = ρ y x)
    (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (μ ν η : V → ℝ) (hμ : MarkovMixing.IsDist μ) (hν : MarkovMixing.IsDist ν)
    (hη : MarkovMixing.IsDist η) :
    (∃ q : V × V → ℝ, MarkovMixing.IsCoupling μ ν q ∧
      MarkovMixing.transportDist ρ μ ν = ∑ p : V × V, ρ p.1 p.2 * q p) ∧
    MarkovMixing.transportDist ρ μ η ≤
      MarkovMixing.transportDist ρ μ ν + MarkovMixing.transportDist ρ ν η := by
  classical
  refine ⟨exists_optimal hρ0 hμ hν, ?_⟩
  obtain ⟨q1, hq1, hq1val⟩ := exists_optimal hρ0 hμ hν
  obtain ⟨q2, hq2, hq2val⟩ := exists_optimal hρ0 hν hη
  have hz1 : ∀ x y : V, ν y = 0 → q1 (x, y) = 0 := by
    intro x y hy
    have hsum : ∑ x', q1 (x', y) = 0 := by rw [hq1.2.2 y, hy]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq1.1.1 (i, y))).mp hsum x
      (Finset.mem_univ x)
  have hz2 : ∀ y z : V, ν y = 0 → q2 (y, z) = 0 := by
    intro y z hy
    have hsum : ∑ z', q2 (y, z') = 0 := by rw [hq2.2.1 y, hy]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq2.1.1 (y, i))).mp hsum z
      (Finset.mem_univ z)
  set Y : Finset V := Finset.univ.filter (fun y : V => ν y ≠ 0) with hY_def
  have hYmem : ∀ y ∈ Y, ν y ≠ 0 := by
    intro y hy
    rw [hY_def, Finset.mem_filter] at hy
    exact hy.2
  have hYpos : ∀ y ∈ Y, 0 < ν y := fun y hy => lt_of_le_of_ne (hν.1 y) (Ne.symm (hYmem y hy))
  have hYsum : ∀ f : V → ℝ, (∀ y, ν y = 0 → f y = 0) → ∑ y ∈ Y, f y = ∑ y, f y := by
    intro f hf
    rw [hY_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ν y = 0
    · simp [h, hf y h]
    · simp [h]
  set q : V × V → ℝ := fun p => ∑ y ∈ Y, q1 (p.1, y) * q2 (y, p.2) / ν y with hq_def
  have hqnn : ∀ p, 0 ≤ q p := by
    intro p
    refine Finset.sum_nonneg fun y hy => ?_
    exact div_nonneg (mul_nonneg (hq1.1.1 _) (hq2.1.1 _)) (hYpos y hy).le
  have hrow : ∀ x, ∑ z, q (x, z) = μ x := by
    intro x
    show ∑ z, ∑ y ∈ Y, q1 (x, y) * q2 (y, z) / ν y = μ x
    rw [Finset.sum_comm]
    have e : ∀ y ∈ Y, ∑ z, q1 (x, y) * q2 (y, z) / ν y = q1 (x, y) := by
      intro y hy
      have hνy : ν y ≠ 0 := hYmem y hy
      have e2 : ∀ z : V, q1 (x, y) * q2 (y, z) / ν y = q1 (x, y) / ν y * q2 (y, z) :=
        fun z => by ring
      rw [Finset.sum_congr rfl (fun z _ => e2 z), ← Finset.mul_sum, hq2.2.1 y]
      field_simp
    rw [Finset.sum_congr rfl e, hYsum (fun y => q1 (x, y)) (fun y hy => hz1 x y hy), hq1.2.1 x]
  have hcol : ∀ z, ∑ x, q (x, z) = η z := by
    intro z
    show ∑ x, ∑ y ∈ Y, q1 (x, y) * q2 (y, z) / ν y = η z
    rw [Finset.sum_comm]
    have e : ∀ y ∈ Y, ∑ x, q1 (x, y) * q2 (y, z) / ν y = q2 (y, z) := by
      intro y hy
      have hνy : ν y ≠ 0 := hYmem y hy
      have e2 : ∀ x : V, q1 (x, y) * q2 (y, z) / ν y = q2 (y, z) / ν y * q1 (x, y) :=
        fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, hq1.2.2 y]
      field_simp
    rw [Finset.sum_congr rfl e, hYsum (fun y => q2 (y, z)) (fun y hy => hz2 y z hy), hq2.2.2 z]
  have hqone : ∑ p : V × V, q p = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hrow x), hμ.2]
  have hqcoup : MarkovMixing.IsCoupling μ η q := ⟨⟨hqnn, hqone⟩, hrow, hcol⟩
  -- the cost of the glued coupling
  have hT1 : ∑ x : V, ∑ z : V, ∑ y ∈ Y, ρ x y * (q1 (x, y) * q2 (y, z) / ν y)
      = ∑ p : V × V, ρ p.1 p.2 * q1 p := by
    have e1 : ∀ x : V, ∑ z : V, ∑ y ∈ Y, ρ x y * (q1 (x, y) * q2 (y, z) / ν y)
        = ∑ y ∈ Y, ρ x y * q1 (x, y) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hνy : ν y ≠ 0 := hYmem y hy
      have e2 : ∀ z : V, ρ x y * (q1 (x, y) * q2 (y, z) / ν y)
          = ρ x y * q1 (x, y) / ν y * q2 (y, z) := fun z => by ring
      rw [Finset.sum_congr rfl (fun z _ => e2 z), ← Finset.mul_sum, hq2.2.1 y]
      field_simp
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine hYsum (fun y => ρ x y * q1 (x, y)) (fun y hy => ?_)
    show ρ x y * q1 (x, y) = 0
    rw [hz1 x y hy]; ring
  have hT2 : ∑ x : V, ∑ z : V, ∑ y ∈ Y, ρ y z * (q1 (x, y) * q2 (y, z) / ν y)
      = ∑ p : V × V, ρ p.1 p.2 * q2 p := by
    rw [Finset.sum_comm]
    have e1 : ∀ z : V, ∑ x : V, ∑ y ∈ Y, ρ y z * (q1 (x, y) * q2 (y, z) / ν y)
        = ∑ y ∈ Y, ρ y z * q2 (y, z) := by
      intro z
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hνy : ν y ≠ 0 := hYmem y hy
      have e2 : ∀ x : V, ρ y z * (q1 (x, y) * q2 (y, z) / ν y)
          = ρ y z * q2 (y, z) / ν y * q1 (x, y) := fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, hq1.2.2 y]
      field_simp
    rw [Finset.sum_congr rfl (fun z _ => e1 z), Finset.sum_comm, Fintype.sum_prod_type]
    refine hYsum (fun y => ∑ z, ρ y z * q2 (y, z)) (fun y hy => ?_)
    show ∑ z, ρ y z * q2 (y, z) = 0
    exact Finset.sum_eq_zero fun z _ => by rw [hz2 y z hy]; ring
  have hcost : ∑ p : V × V, ρ p.1 p.2 * q p
      ≤ (∑ p : V × V, ρ p.1 p.2 * q1 p) + ∑ p : V × V, ρ p.1 p.2 * q2 p := by
    have hA : ∀ x z : V, ρ x z * q (x, z)
        ≤ ∑ y ∈ Y, (ρ x y + ρ y z) * (q1 (x, y) * q2 (y, z) / ν y) := by
      intro x z
      show ρ x z * ∑ y ∈ Y, q1 (x, y) * q2 (y, z) / ν y ≤ _
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y hy => ?_
      have hterm : 0 ≤ q1 (x, y) * q2 (y, z) / ν y :=
        div_nonneg (mul_nonneg (hq1.1.1 _) (hq2.1.1 _)) (hYpos y hy).le
      exact mul_le_mul_of_nonneg_right (hρtri x y z) hterm
    have hB : ∑ p : V × V, ρ p.1 p.2 * q p
        ≤ ∑ x : V, ∑ z : V, ∑ y ∈ Y, (ρ x y + ρ y z) * (q1 (x, y) * q2 (y, z) / ν y) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hA x z
    have hC : ∑ x : V, ∑ z : V, ∑ y ∈ Y, (ρ x y + ρ y z) * (q1 (x, y) * q2 (y, z) / ν y)
        = (∑ x : V, ∑ z : V, ∑ y ∈ Y, ρ x y * (q1 (x, y) * q2 (y, z) / ν y))
          + ∑ x : V, ∑ z : V, ∑ y ∈ Y, ρ y z * (q1 (x, y) * q2 (y, z) / ν y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hC, hT1, hT2] at hB
    exact hB
  have hmem : (∑ p : V × V, ρ p.1 p.2 * q p) ∈
      {e : ℝ | ∃ q' : V × V → ℝ, MarkovMixing.IsCoupling μ η q' ∧
        e = ∑ p : V × V, ρ p.1 p.2 * q' p} := ⟨q, hqcoup, rfl⟩
  calc MarkovMixing.transportDist ρ μ η ≤ ∑ p : V × V, ρ p.1 p.2 * q p :=
        csInf_le (bddBelow_costs hρ0 μ η) hmem
    _ ≤ (∑ p : V × V, ρ p.1 p.2 * q1 p) + ∑ p : V × V, ρ p.1 p.2 * q2 p := hcost
    _ = MarkovMixing.transportDist ρ μ ν + MarkovMixing.transportDist ρ ν η := by
        rw [hq1val, hq2val]
