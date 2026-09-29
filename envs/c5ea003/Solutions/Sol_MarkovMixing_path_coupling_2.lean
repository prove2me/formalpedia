-- Prove2me | solution 2 for MarkovMixing.path_coupling
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T18:06:29.202211+00:00
-- url     : https://prove2.me/submissions/3d244ea5-131d-449c-888b-e4b0785c774e

import Definitions.Def_mm_transport
import Theorems.Thm_MarkovMixing_transport_metric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace PathCoup

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {G : SimpleGraph V} {ℓ : V → V → ℝ}

lemma walkLength_nonneg (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    {x y : V} (w : G.Walk x y) : 0 ≤ walkLength ℓ w := by
  refine List.sum_nonneg ?_
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨d, hd, rfl⟩ := ha
  linarith [hℓ1 d.toProd.1 d.toProd.2 d.adj]

lemma walkLength_cons {x b y : V} (h : G.Adj x b) (w : G.Walk b y) :
    walkLength ℓ (SimpleGraph.Walk.cons h w) = ℓ x b + walkLength ℓ w := by
  show ((SimpleGraph.Walk.cons h w).darts.map fun d => ℓ d.toProd.1 d.toProd.2).sum = _
  rw [SimpleGraph.Walk.darts_cons]
  simp [walkLength]

lemma walkLength_append {x y z : V} (w1 : G.Walk x y) (w2 : G.Walk y z) :
    walkLength ℓ (w1.append w2) = walkLength ℓ w1 + walkLength ℓ w2 := by
  show ((w1.append w2).darts.map fun d => ℓ d.toProd.1 d.toProd.2).sum = _
  rw [SimpleGraph.Walk.darts_append]
  simp [walkLength]

lemma walkLength_reverse (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    {x y : V} (w : G.Walk x y) : walkLength ℓ w.reverse = walkLength ℓ w := by
  show ((w.reverse).darts.map fun d => ℓ d.toProd.1 d.toProd.2).sum = _
  rw [SimpleGraph.Walk.darts_reverse]
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  show (List.map ((fun d : G.Dart => ℓ d.toProd.1 d.toProd.2) ∘ SimpleGraph.Dart.symm)
    w.darts).sum = _
  congr 1
  refine List.map_congr_left ?_
  intro d _
  show ℓ d.symm.toProd.1 d.symm.toProd.2 = ℓ d.toProd.1 d.toProd.2
  exact hℓsymm _ _

section Metric

variable (G ℓ)

lemma set_nonempty (hconn : G.Connected) (x y : V) :
    {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w}.Nonempty := by
  obtain ⟨w⟩ := hconn.preconnected x y
  exact ⟨walkLength ℓ w, w, rfl⟩

lemma set_bddBelow (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x y : V) :
    BddBelow {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, rfl⟩
  exact walkLength_nonneg hℓ1 w

lemma pathMetric_le (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) {x y : V} (w : G.Walk x y) :
    pathMetric G ℓ x y ≤ walkLength ℓ w :=
  csInf_le (set_bddBelow G ℓ hℓ1 x y) ⟨w, rfl⟩

lemma pathMetric_nonneg (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (x y : V) : 0 ≤ pathMetric G ℓ x y := by
  refine le_csInf (set_nonempty G ℓ hconn x y) ?_
  rintro r ⟨w, rfl⟩
  exact walkLength_nonneg hℓ1 w

lemma pathMetric_self (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x : V) :
    pathMetric G ℓ x x = 0 := by
  refine le_antisymm ?_ (pathMetric_nonneg G ℓ hconn hℓ1 x x)
  have := pathMetric_le G ℓ hℓ1 (SimpleGraph.Walk.nil : G.Walk x x)
  simpa [walkLength] using this

lemma pathMetric_triangle (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (x y z : V) : pathMetric G ℓ x z ≤ pathMetric G ℓ x y + pathMetric G ℓ y z := by
  have h1 : ∀ w1 : G.Walk x y, pathMetric G ℓ x z - pathMetric G ℓ y z ≤ walkLength ℓ w1 := by
    intro w1
    have h2 : ∀ w2 : G.Walk y z, pathMetric G ℓ x z - walkLength ℓ w1 ≤ walkLength ℓ w2 := by
      intro w2
      have := pathMetric_le G ℓ hℓ1 (w1.append w2)
      rw [walkLength_append] at this
      linarith
    have h3 : pathMetric G ℓ x z - walkLength ℓ w1 ≤ pathMetric G ℓ y z := by
      refine le_csInf (set_nonempty G ℓ hconn y z) ?_
      rintro r ⟨w2, rfl⟩
      exact h2 w2
    linarith
  have h4 : pathMetric G ℓ x z - pathMetric G ℓ y z ≤ pathMetric G ℓ x y := by
    refine le_csInf (set_nonempty G ℓ hconn x y) ?_
    rintro r ⟨w1, rfl⟩
    exact h1 w1
  linarith

lemma pathMetric_symm (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x) (x y : V) :
    pathMetric G ℓ x y = pathMetric G ℓ y x := by
  have key : ∀ a b : V, pathMetric G ℓ a b ≤ pathMetric G ℓ b a := by
    intro a b
    refine le_csInf (set_nonempty G ℓ hconn b a) ?_
    rintro r ⟨w, rfl⟩
    have := pathMetric_le G ℓ hℓ1 w.reverse
    rwa [walkLength_reverse hℓsymm] at this
  exact le_antisymm (key x y) (key y x)

lemma pathMetric_eq_zero (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (x y : V) : pathMetric G ℓ x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have hone : ∀ w : G.Walk x y, (1 : ℝ) ≤ walkLength ℓ w := by
      intro w
      cases w with
      | nil => exact absurd rfl hxy
      | cons hadj w' =>
        rw [walkLength_cons]
        linarith [hℓ1 _ _ hadj, walkLength_nonneg hℓ1 w']
    have h5 : (1:ℝ) ≤ pathMetric G ℓ x y := by
      refine le_csInf (set_nonempty G ℓ hconn x y) ?_
      rintro r ⟨w, rfl⟩
      exact hone w
    rw [h] at h5
    linarith
  · rintro rfl
    exact pathMetric_self G ℓ hconn hℓ1 x

end Metric

end PathCoup

namespace PathCoup2

open PathCoup

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma bddBelow_costs {ρ : V → V → ℝ} (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (μ ν : V → ℝ) :
    BddBelow {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      e = ∑ p : V × V, ρ p.1 p.2 * q p} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hρ0 _ _) (hq.1.1 p)

lemma rowDist_isDist {P : Matrix V V ℝ} (hP : IsStochastic P) (x : V) :
    IsDist (rowDist P 1 x) := by
  constructor
  · intro y
    show (0:ℝ) ≤ (P ^ 1) x y
    rw [pow_one]
    exact hP.1 x y
  · show ∑ y, (P ^ 1) x y = 1
    rw [pow_one]
    exact hP.2 x

lemma transportDist_self {ρ : V → V → ℝ} (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρself : ∀ x : V, ρ x x = 0) {μ : V → ℝ} (hμ : IsDist μ) :
    transportDist ρ μ μ ≤ 0 := by
  classical
  set q : V × V → ℝ := fun p => if p.1 = p.2 then μ p.1 else 0 with hq_def
  have hcoup : IsCoupling μ μ q := by
    refine ⟨⟨fun p => ?_, ?_⟩, ?_, ?_⟩
    · by_cases h : p.1 = p.2 <;> simp [hq_def, h, hμ.1]
    · show ∑ p : V × V, (if p.1 = p.2 then μ p.1 else 0) = 1
      rw [Fintype.sum_prod_type]
      have e : ∀ x : V, ∑ y, (if x = y then μ x else 0) = μ x := by
        intro x
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [Ne.symm hb])]
        simp
      rw [Finset.sum_congr rfl (fun x _ => e x), hμ.2]
    · intro x
      show ∑ y, (if x = y then μ x else 0) = μ x
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [Ne.symm hb])]
      simp
    · intro y
      show ∑ x, (if x = y then μ x else 0) = μ y
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y) (fun b _ hb => by simp [hb])]
      simp
  have hcost : ∑ p : V × V, ρ p.1 p.2 * q p = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases h : p.1 = p.2
    · rw [h, hρself, zero_mul]
    · simp [hq_def, h]
  have := csInf_le (bddBelow_costs hρ0 μ μ) ⟨q, hcoup, rfl⟩
  rw [hcost] at this
  exact this

end PathCoup2

open PathCoup PathCoup2

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    (α : ℝ) (hα : 0 < α)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, MarkovMixing.IsCoupling (MarkovMixing.rowDist P 1 x)
          (MarkovMixing.rowDist P 1 y) q ∧
        ∑ p : V × V, q p * MarkovMixing.pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    (μ ν : V → ℝ) (hμ : MarkovMixing.IsDist μ) (hν : MarkovMixing.IsDist ν) :
    MarkovMixing.transportDist (MarkovMixing.pathMetric G ℓ)
        (Matrix.vecMul μ P) (Matrix.vecMul ν P) ≤
      Real.exp (-α) * MarkovMixing.transportDist (MarkovMixing.pathMetric G ℓ) μ ν := by
  classical
  set ρ : V → V → ℝ := MarkovMixing.pathMetric G ℓ with hρ_def
  have hρ0 : ∀ x y : V, 0 ≤ ρ x y := pathMetric_nonneg G ℓ hconn hℓ1
  have hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y := pathMetric_eq_zero G ℓ hconn hℓ1
  have hρsymm : ∀ x y : V, ρ x y = ρ y x := pathMetric_symm G ℓ hconn hℓ1 hℓsymm
  have hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z := pathMetric_triangle G ℓ hconn hℓ1
  have hρself : ∀ x : V, ρ x x = 0 := fun x => pathMetric_self G ℓ hconn hℓ1 x
  have hexp : (0:ℝ) < Real.exp (-α) := Real.exp_pos _
  -- contraction along a walk
  have hwalk : ∀ {x y : V} (w : G.Walk x y),
      MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 x) (MarkovMixing.rowDist P 1 y)
        ≤ Real.exp (-α) * walkLength ℓ w := by
    intro x y w
    induction w with
    | @nil u =>
      have h0 : MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 u)
          (MarkovMixing.rowDist P 1 u) ≤ 0 :=
        transportDist_self hρ0 hρself (rowDist_isDist hP u)
      have hzero : walkLength ℓ (SimpleGraph.Walk.nil : G.Walk u u) = 0 := by
        simp [walkLength]
      rw [hzero, mul_zero]
      exact h0
    | @cons a b c hadj w' ih =>
      obtain ⟨qe, hqe, hqecost⟩ := hedge a b hadj
      have hstep : MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 a)
          (MarkovMixing.rowDist P 1 b) ≤ Real.exp (-α) * ℓ a b := by
        refine le_trans (csInf_le (bddBelow_costs hρ0 _ _) ⟨qe, hqe, rfl⟩) ?_
        refine le_trans (le_of_eq ?_) hqecost
        exact Finset.sum_congr rfl fun p _ => by ring
      have htri := (MarkovMixing.transport_metric ρ hρ0 hρeq hρsymm hρtri
        (MarkovMixing.rowDist P 1 a) (MarkovMixing.rowDist P 1 b) (MarkovMixing.rowDist P 1 c)
        (rowDist_isDist hP a) (rowDist_isDist hP b) (rowDist_isDist hP c)).2
      rw [walkLength_cons]
      calc MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 a)
            (MarkovMixing.rowDist P 1 c)
          ≤ MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 a)
              (MarkovMixing.rowDist P 1 b)
            + MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 b)
              (MarkovMixing.rowDist P 1 c) := htri
        _ ≤ Real.exp (-α) * ℓ a b + Real.exp (-α) * walkLength ℓ w' := by
            exact add_le_add hstep ih
        _ = Real.exp (-α) * (ℓ a b + walkLength ℓ w') := by ring
  -- contraction on pairs
  have hpairbd : ∀ x y : V,
      MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 x) (MarkovMixing.rowDist P 1 y)
        ≤ Real.exp (-α) * ρ x y := by
    intro x y
    have h1 : MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 x)
        (MarkovMixing.rowDist P 1 y) / Real.exp (-α) ≤ ρ x y := by
      refine le_csInf (set_nonempty G ℓ hconn x y) ?_
      rintro s ⟨w, rfl⟩
      rw [div_le_iff₀ hexp]
      calc MarkovMixing.transportDist ρ (MarkovMixing.rowDist P 1 x)
            (MarkovMixing.rowDist P 1 y) ≤ Real.exp (-α) * walkLength ℓ w := hwalk w
        _ = walkLength ℓ w * Real.exp (-α) := by ring
    rw [div_le_iff₀ hexp] at h1
    linarith
  -- optimal coupling of μ and ν, and the pairwise couplings
  obtain ⟨q0, hq0, hq0val⟩ :=
    (MarkovMixing.transport_metric ρ hρ0 hρeq hρsymm hρtri μ ν μ hμ hν hμ).1
  have hpair : ∀ x y : V, ∃ r : V × V → ℝ,
      MarkovMixing.IsCoupling (MarkovMixing.rowDist P 1 x) (MarkovMixing.rowDist P 1 y) r ∧
        ∑ p : V × V, ρ p.1 p.2 * r p ≤ Real.exp (-α) * ρ x y := by
    intro x y
    obtain ⟨r, hr, hrval⟩ := (MarkovMixing.transport_metric ρ hρ0 hρeq hρsymm hρtri
      (MarkovMixing.rowDist P 1 x) (MarkovMixing.rowDist P 1 y) (MarkovMixing.rowDist P 1 x)
      (rowDist_isDist hP x) (rowDist_isDist hP y) (rowDist_isDist hP x)).1
    refine ⟨r, hr, ?_⟩
    rw [← hrval]
    exact hpairbd x y
  choose r hr hrcost using hpair
  set Q : V × V → ℝ := fun p => ∑ x, ∑ y, q0 (x, y) * r x y p with hQ_def
  have hProw : ∀ x z : V, MarkovMixing.rowDist P 1 x z = P x z := by
    intro x z
    show (P ^ 1) x z = P x z
    rw [pow_one]
  have hQnn : ∀ p, 0 ≤ Q p :=
    fun p => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hq0.1.1 (x, y)) ((hr x y).1.1 p)
  have hQrow : ∀ z, ∑ w, Q (z, w) = Matrix.vecMul μ P z := by
    intro z
    show ∑ w, ∑ x, ∑ y, q0 (x, y) * r x y (z, w) = ∑ x, μ x * P x z
    rw [Finset.sum_comm]
    have e : ∀ x : V, ∑ w, ∑ y, q0 (x, y) * r x y (z, w) = μ x * P x z := by
      intro x
      rw [Finset.sum_comm]
      have e2 : ∀ y : V, ∑ w, q0 (x, y) * r x y (z, w) = q0 (x, y) * P x z := by
        intro y
        rw [← Finset.mul_sum, (hr x y).2.1 z, hProw]
      rw [Finset.sum_congr rfl (fun y _ => e2 y), ← Finset.sum_mul, hq0.2.1 x]
    rw [Finset.sum_congr rfl (fun x _ => e x)]
  have hQcol : ∀ w, ∑ z, Q (z, w) = Matrix.vecMul ν P w := by
    intro w
    show ∑ z, ∑ x, ∑ y, q0 (x, y) * r x y (z, w) = ∑ y, ν y * P y w
    rw [Finset.sum_comm]
    have e : ∀ x : V, ∑ z, ∑ y, q0 (x, y) * r x y (z, w) = ∑ y, q0 (x, y) * P y w := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.mul_sum, (hr x y).2.2 w, hProw]
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, hq0.2.2 y]
  have hQone : ∑ p : V × V, Q p = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hQrow z)]
    show ∑ z, ∑ x, μ x * P x z = 1
    rw [Finset.sum_comm]
    have e : ∀ x : V, ∑ z, μ x * P x z = μ x := by
      intro x; rw [← Finset.mul_sum, hP.2 x, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => e x), hμ.2]
  have hQcoup : MarkovMixing.IsCoupling (Matrix.vecMul μ P) (Matrix.vecMul ν P) Q :=
    ⟨⟨hQnn, hQone⟩, hQrow, hQcol⟩
  have hQcost : ∑ p : V × V, ρ p.1 p.2 * Q p
      ≤ Real.exp (-α) * ∑ p : V × V, ρ p.1 p.2 * q0 p := by
    have e1 : ∑ p : V × V, ρ p.1 p.2 * Q p
        = ∑ x, ∑ y, q0 (x, y) * ∑ p : V × V, ρ p.1 p.2 * r x y p := by
      have e3 : ∀ p : V × V, ρ p.1 p.2 * Q p
          = ∑ x, ∑ y, q0 (x, y) * (ρ p.1 p.2 * r x y p) := by
        intro p
        show ρ p.1 p.2 * (∑ x, ∑ y, q0 (x, y) * r x y p) = _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [Finset.sum_congr rfl (fun p _ => e3 p), Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.mul_sum]
    rw [e1]
    have e5 : ∑ x, ∑ y, q0 (x, y) * ∑ p : V × V, ρ p.1 p.2 * r x y p
        ≤ ∑ x, ∑ y, q0 (x, y) * (Real.exp (-α) * ρ x y) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      exact mul_le_mul_of_nonneg_left (hrcost x y) (hq0.1.1 (x, y))
    refine le_trans e5 ?_
    have e6 : ∑ x, ∑ y, q0 (x, y) * (Real.exp (-α) * ρ x y)
        = Real.exp (-α) * ∑ p : V × V, ρ p.1 p.2 * q0 p := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e6]
  calc MarkovMixing.transportDist ρ (Matrix.vecMul μ P) (Matrix.vecMul ν P)
      ≤ ∑ p : V × V, ρ p.1 p.2 * Q p :=
        csInf_le (bddBelow_costs hρ0 _ _) ⟨Q, hQcoup, rfl⟩
    _ ≤ Real.exp (-α) * ∑ p : V × V, ρ p.1 p.2 * q0 p := hQcost
    _ = Real.exp (-α) * MarkovMixing.transportDist ρ μ ν := by rw [hq0val]
