-- Prove2me | solution 1 for MarkovMixing.transport_metric
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T17:56:41.332435+00:00
-- url     : https://prove2.me/submissions/05e03601-cf0c-4a07-a94b-5fb4f8d66ed3

import Definitions.Def_mm_transport
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid

/-!
# The transportation metric is attained, and satisfies the triangle inequality

Two independent facts about the Kantorovich transportation distance

`transportDist ρ μ ν = sInf { ∑ ρ(x,y) q(x,y) : q a coupling of μ and ν }`

on a finite state space.

* **Attainment.**  The set of couplings of `μ` and `ν` is a nonempty compact
  subset of `ℝ^(V × V)` (it is closed, and contained in the cube `[0,1]^(V×V)`),
  and the cost is a continuous linear functional, so the extreme value theorem
  produces a minimiser.  The product coupling `q(x,y) = μ(x) ν(y)` witnesses
  nonemptiness.

* **Triangle inequality.**  This is the *gluing lemma*: given couplings `q₁` of
  `(μ,ν)` and `q₂` of `(ν,η)`, the measure

  `r(x,z) = ∑_y q₁(x,y) q₂(y,z) / ν(y)`

  is a coupling of `(μ,η)`.  (Lean's `x / 0 = 0` convention takes care of the
  atoms with `ν(y) = 0`, which carry no `q₁`- or `q₂`-mass anyway.)  The
  triangle inequality for `ρ` then bounds its cost by the sum of the two costs.
-/

namespace MarkovMixing

open scoped BigOperators

private lemma sum_swap_aux {V : Type*} [Fintype V] (g : V → V → ℝ) :
    ∑ a : V, ∑ b : V, g a b = ∑ b : V, ∑ a : V, g a b :=
  Finset.sum_comm

/-- The set of costs of couplings is bounded below by `0`. -/
private lemma transport_bddBelow {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (μ ν : V → ℝ) :
    BddBelow {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      e = ∑ p : V × V, ρ p.1 p.2 * q p} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hρ0 _ _) (hq.1.1 p)

/-- **Attainment**: the infimum defining `transportDist` is a minimum. -/
private lemma transport_attained {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      transportDist ρ μ ν = ∑ p : V × V, ρ p.1 p.2 * q p := by
  classical
  -- the product coupling shows the coupling polytope is nonempty
  have hprod : IsCoupling μ ν (fun p : V × V => μ p.1 * ν p.2) := by
    refine ⟨⟨fun p => mul_nonneg (hμ.1 _) (hν.1 _), ?_⟩, ?_, ?_⟩
    · rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, hν.2, mul_one, hμ.2]
    · intro x
      simp only [← Finset.mul_sum, hν.2, mul_one]
    · intro y
      simp only [← Finset.sum_mul, hμ.2, one_mul]
  -- the coupling polytope sits inside the unit cube
  have hsub : {q : V × V → ℝ | IsCoupling μ ν q} ⊆
      Set.univ.pi fun _ : V × V => Set.Icc (0 : ℝ) 1 := by
    intro q hq
    refine Set.mem_univ_pi.mpr fun p => ⟨hq.1.1 p, ?_⟩
    have hle := Finset.single_le_sum (f := q) (fun i _ => hq.1.1 i) (Finset.mem_univ p)
    rwa [hq.1.2] at hle
  -- and it is closed
  have hcl : IsClosed {q : V × V → ℝ | IsCoupling μ ν q} := by
    have hset : {q : V × V → ℝ | IsCoupling μ ν q} =
        (⋂ p : V × V, {q : V × V → ℝ | 0 ≤ q p}) ∩
        ({q : V × V → ℝ | ∑ p : V × V, q p = 1} ∩
          ((⋂ x : V, {q : V × V → ℝ | ∑ y : V, q (x, y) = μ x}) ∩
            (⋂ y : V, {q : V × V → ℝ | ∑ x : V, q (x, y) = ν y}))) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, IsCoupling, IsDist]
      tauto
    rw [hset]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
    · exact isClosed_eq (continuous_finsetSum _ fun p _ => continuous_apply p) continuous_const
    · exact isClosed_iInter fun x => isClosed_eq
        (continuous_finsetSum _ fun y _ => continuous_apply (x, y)) continuous_const
    · exact isClosed_iInter fun y => isClosed_eq
        (continuous_finsetSum _ fun x _ => continuous_apply (x, y)) continuous_const
  have hK : IsCompact {q : V × V → ℝ | IsCoupling μ ν q} :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hcl hsub
  have hcont : Continuous fun q : V × V → ℝ => ∑ p : V × V, ρ p.1 p.2 * q p :=
    continuous_finsetSum _ fun p _ => (continuous_apply p).const_mul _
  obtain ⟨q₀, hq₀K, hmin⟩ := hK.exists_isMinOn ⟨_, hprod⟩ hcont.continuousOn
  refine ⟨q₀, hq₀K, ?_⟩
  refine IsLeast.csInf_eq ⟨⟨q₀, hq₀K, rfl⟩, ?_⟩
  rintro e ⟨q, hq, rfl⟩
  exact isMinOn_iff.mp hmin q hq

/-- The elementary algebra of the glued measure `w x y z = q₁(x,y) q₂(y,z)/ν(y)`. -/
private lemma glue_props {V : Type*} [Fintype V] [DecidableEq V]
    (ν : V → ℝ) (q₁ q₂ : V × V → ℝ)
    (hν0 : ∀ y : V, 0 ≤ ν y)
    (h1nn : ∀ p : V × V, 0 ≤ q₁ p) (h2nn : ∀ p : V × V, 0 ≤ q₂ p)
    (h1col : ∀ y : V, ∑ x : V, q₁ (x, y) = ν y)
    (h2row : ∀ y : V, ∑ z : V, q₂ (y, z) = ν y) :
    (∀ x y z : V, 0 ≤ q₁ (x, y) * q₂ (y, z) / ν y) ∧
    (∀ x y : V, ∑ z : V, q₁ (x, y) * q₂ (y, z) / ν y = q₁ (x, y)) ∧
    (∀ y z : V, ∑ x : V, q₁ (x, y) * q₂ (y, z) / ν y = q₂ (y, z)) := by
  classical
  have hz1 : ∀ x y : V, ν y = 0 → q₁ (x, y) = 0 := by
    intro x y hy
    have hs := h1col y
    rw [hy] at hs
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h1nn (i, y)).mp hs x (Finset.mem_univ x)
  have hz2 : ∀ y z : V, ν y = 0 → q₂ (y, z) = 0 := by
    intro y z hy
    have hs := h2row y
    rw [hy] at hs
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h2nn (y, i)).mp hs z (Finset.mem_univ z)
  refine ⟨fun x y z => div_nonneg (mul_nonneg (h1nn _) (h2nn _)) (hν0 y), ?_, ?_⟩
  · intro x y
    by_cases hy : ν y = 0
    · simp [hy, hz1 x y hy]
    · have hstep : ∑ z : V, q₁ (x, y) * q₂ (y, z) / ν y
          = q₁ (x, y) / ν y * ∑ z : V, q₂ (y, z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [hstep, h2row y, div_mul_cancel₀ _ hy]
  · intro y z
    by_cases hy : ν y = 0
    · simp [hy, hz2 y z hy]
    · have hstep : ∑ x : V, q₁ (x, y) * q₂ (y, z) / ν y
          = (∑ x : V, q₁ (x, y)) * (q₂ (y, z) / ν y) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [hstep, h1col y, mul_comm, div_mul_cancel₀ _ hy]

/-- The glued measure is a coupling of the outer two distributions. -/
private lemma glue_coupling {V : Type*} [Fintype V] [DecidableEq V]
    (μ η : V → ℝ) (hμ : IsDist μ) (w : V → V → V → ℝ) (q₁ q₂ : V × V → ℝ)
    (hwnn : ∀ x y z : V, 0 ≤ w x y z)
    (hwz : ∀ x y : V, ∑ z : V, w x y z = q₁ (x, y))
    (hwx : ∀ y z : V, ∑ x : V, w x y z = q₂ (y, z))
    (h1row : ∀ x : V, ∑ y : V, q₁ (x, y) = μ x)
    (h2col : ∀ z : V, ∑ y : V, q₂ (y, z) = η z) :
    IsCoupling μ η (fun p : V × V => ∑ y : V, w p.1 y p.2) := by
  have hmargμ : ∀ x : V, ∑ z : V, (∑ y : V, w x y z) = μ x := by
    intro x
    rw [sum_swap_aux fun z y => w x y z]
    simp only [hwz]
    exact h1row x
  have hmargη : ∀ z : V, ∑ x : V, (∑ y : V, w x y z) = η z := by
    intro z
    rw [sum_swap_aux fun x y => w x y z]
    simp only [hwx]
    exact h2col z
  refine ⟨⟨fun p => Finset.sum_nonneg fun y _ => hwnn _ _ _, ?_⟩, hmargμ, hmargη⟩
  rw [Fintype.sum_prod_type]
  simp only [hmargμ]
  exact hμ.2

/-- The cost of the glued coupling is at most the sum of the two costs. -/
private lemma glue_cost {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (w : V → V → V → ℝ) (q₁ q₂ : V × V → ℝ)
    (hwnn : ∀ x y z : V, 0 ≤ w x y z)
    (hwz : ∀ x y : V, ∑ z : V, w x y z = q₁ (x, y))
    (hwx : ∀ y z : V, ∑ x : V, w x y z = q₂ (y, z)) :
    ∑ p : V × V, ρ p.1 p.2 * (∑ y : V, w p.1 y p.2) ≤
      (∑ p : V × V, ρ p.1 p.2 * q₁ p) + ∑ p : V × V, ρ p.1 p.2 * q₂ p := by
  have hL : ∑ p : V × V, ρ p.1 p.2 * (∑ y : V, w p.1 y p.2)
      = ∑ x : V, ∑ z : V, ∑ y : V, ρ x z * w x y z := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
      Finset.mul_sum _ _ _
  have hUb : ∑ x : V, ∑ z : V, ∑ y : V, ρ x z * w x y z
      ≤ ∑ x : V, ∑ z : V, ∑ y : V, (ρ x y + ρ y z) * w x y z :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_right (hρtri x y z) (hwnn x y z)
  have hSplit : ∑ x : V, ∑ z : V, ∑ y : V, (ρ x y + ρ y z) * w x y z
      = (∑ x : V, ∑ z : V, ∑ y : V, ρ x y * w x y z)
        + ∑ x : V, ∑ z : V, ∑ y : V, ρ y z * w x y z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => add_mul _ _ _
  have hA : ∑ x : V, ∑ z : V, ∑ y : V, ρ x y * w x y z
      = ∑ p : V × V, ρ p.1 p.2 * q₁ p := by
    have a1 : ∑ x : V, ∑ z : V, ∑ y : V, ρ x y * w x y z
        = ∑ x : V, ∑ y : V, ∑ z : V, ρ x y * w x y z :=
      Finset.sum_congr rfl fun x _ => sum_swap_aux fun z y => ρ x y * w x y z
    rw [a1, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [← Finset.mul_sum, hwz x y]
  have hB : ∑ x : V, ∑ z : V, ∑ y : V, ρ y z * w x y z
      = ∑ p : V × V, ρ p.1 p.2 * q₂ p := by
    have b1 : ∑ x : V, ∑ z : V, ∑ y : V, ρ y z * w x y z
        = ∑ x : V, ∑ y : V, ∑ z : V, ρ y z * w x y z :=
      Finset.sum_congr rfl fun x _ => sum_swap_aux fun z y => ρ y z * w x y z
    have b2 : ∑ x : V, ∑ y : V, ∑ z : V, ρ y z * w x y z
        = ∑ y : V, ∑ x : V, ∑ z : V, ρ y z * w x y z :=
      sum_swap_aux fun x y => ∑ z : V, ρ y z * w x y z
    have b3 : ∑ y : V, ∑ x : V, ∑ z : V, ρ y z * w x y z
        = ∑ y : V, ∑ z : V, ∑ x : V, ρ y z * w x y z :=
      Finset.sum_congr rfl fun y _ => sum_swap_aux fun x z => ρ y z * w x y z
    rw [b1, b2, b3, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by
      rw [← Finset.mul_sum, hwx y z]
  rw [hL]
  calc ∑ x : V, ∑ z : V, ∑ y : V, ρ x z * w x y z
      ≤ ∑ x : V, ∑ z : V, ∑ y : V, (ρ x y + ρ y z) * w x y z := hUb
    _ = _ := by rw [hSplit, hA, hB]

end MarkovMixing

open MarkovMixing

/-- **Lemma 14.3 and Remark 14.2** (LPW): the transportation distance is
attained by an optimal coupling, and satisfies the triangle inequality. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y)
    (hρsymm : ∀ x y : V, ρ x y = ρ y x)
    (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (μ ν η : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (hη : IsDist η) :
    (∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      transportDist ρ μ ν = ∑ p : V × V, ρ p.1 p.2 * q p) ∧
    transportDist ρ μ η ≤ transportDist ρ μ ν + transportDist ρ ν η := by
  classical
  obtain ⟨q₁, hq₁, hval₁⟩ := transport_attained ρ μ ν hμ hν
  obtain ⟨q₂, hq₂, hval₂⟩ := transport_attained ρ ν η hν hη
  refine ⟨⟨q₁, hq₁, hval₁⟩, ?_⟩
  obtain ⟨hwnn, hwz, hwx⟩ :=
    glue_props ν q₁ q₂ hν.1 hq₁.1.1 hq₂.1.1 hq₁.2.2 hq₂.2.1
  have hrc : IsCoupling μ η
      (fun p : V × V => ∑ y : V, q₁ (p.1, y) * q₂ (y, p.2) / ν y) :=
    glue_coupling μ η hμ (fun x y z => q₁ (x, y) * q₂ (y, z) / ν y) q₁ q₂
      hwnn hwz hwx hq₁.2.1 hq₂.2.2
  have hcost := glue_cost ρ hρtri (fun x y z => q₁ (x, y) * q₂ (y, z) / ν y) q₁ q₂
    hwnn hwz hwx
  have hinf : transportDist ρ μ η ≤
      ∑ p : V × V, ρ p.1 p.2 * (∑ y : V, q₁ (p.1, y) * q₂ (y, p.2) / ν y) :=
    csInf_le (transport_bddBelow ρ hρ0 μ η) ⟨_, hrc, rfl⟩
  rw [hval₁, hval₂]
  exact le_trans hinf hcost

