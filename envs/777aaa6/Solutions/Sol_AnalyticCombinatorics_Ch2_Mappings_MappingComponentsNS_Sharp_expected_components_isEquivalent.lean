-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp.expected_components_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:58.053796+00:00
-- url     : https://prove2.me/submissions/d4381ab5-5726-46bb-ac41-871e9dacaadb

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_MappingComponents
import Mathlib

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Completing the rooted forest count

This file adds a carrier-polymorphic version of the rooted-forest definitions
from `ForestCount.lean`.  The immediate target is the depth-one decomposition:
for a forest whose root set is not all vertices, at least one non-root has a
root as parent.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

noncomputable section

lemma sum_nonempty_finsets_by_card {β : Type*} [DecidableEq β] [Fintype β]
    (f : ℕ → ℕ) :
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
      ∑ i ∈ Finset.range (Fintype.card β),
        Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
  classical
  let U : Finset β := Finset.univ
  have hsub :
      (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
        ∑ S ∈ (Finset.univ : Finset (Finset β)) with S.Nonempty, f S.card := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Finset β)))
        (f := fun S : Finset β => f S.card)
        (p := fun S : Finset β => S.Nonempty))
  have huniv : (Finset.univ : Finset (Finset β)) = U.powerset := by
    ext S
    simp [U]
  have hinner (j : ℕ) :
      (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
        Nat.choose U.card j * (if j = 0 then 0 else f j) := by
    by_cases hj : j = 0
    · subst j
      simp
    · calc
        (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
            ∑ S ∈ U.powersetCard j, f S.card := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hScard : S.card = j := (Finset.mem_powersetCard.mp hS).2
            have hnon : S.Nonempty := by
              rw [← Finset.card_pos, hScard]
              omega
            simp [hnon]
        _ = Nat.choose U.card j • f j := by
            simpa using
              (Finset.sum_powersetCard (n := j) (s := U) (f := f))
        _ = Nat.choose U.card j * f j := by
            simp
        _ = Nat.choose U.card j * (if j = 0 then 0 else f j) := by
            simp [hj]
  calc
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card)
        = ∑ S ∈ U.powerset with S.Nonempty, f S.card := by
          rw [hsub, huniv]
    _ = ∑ S ∈ U.powerset, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          ∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_powerset]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          Nat.choose U.card j * (if j = 0 then 0 else f j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hinner j
    _ = ∑ i ∈ Finset.range U.card, Nat.choose U.card (i + 1) * f (i + 1) := by
          rw [Finset.sum_range_succ']
          simp
    _ = ∑ i ∈ Finset.range (Fintype.card β),
          Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
          simp [U]

end
end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

/-!
# Ramanujan's Q-function for random mappings

This file defines the finite Ramanujan Q-function from Flajolet--Sedgewick,
Chapter II.3.  The intended asymptotic is

`Q(n) ~ sqrt (pi * n / 2)`.

The full Laplace-method asymptotic is not yet present in Mathlib.  This file
records the faithful finite definition and elementary verified bounds that are
used by that proof.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

lemma sum_range_succ_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ))) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]
      ring

lemma sum_range_succ_cast_div (k n : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
  rw [← Finset.sum_div, sum_range_succ_cast]

lemma ramanujanQTerm_nonneg {n k : ℕ} (hk : k ≤ n) :
    0 ≤ ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine Finset.prod_nonneg ?_
  intro j hj
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hjn : j + 1 ≤ n := hjk.trans hk
  by_cases hn : n = 0
  · subst hn
    have : j + 1 ≤ 0 := hjn
    omega
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn
  linarith

lemma ramanujanQTerm_factor_le_exp {n k j : ℕ} (_hk : k ≤ n) (_hj : j ∈ Finset.range k) :
    1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
  have h := Real.add_one_le_exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ)))
  linarith

lemma ramanujanQTerm_le_exp_sum {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
  classical
  unfold ramanujanQTerm
  calc
    (∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤
        ∏ j ∈ Finset.range k, Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hjn : j + 1 ≤ n := hjk.trans hk
        by_cases hn : n = 0
        · subst hn
          have : j + 1 ≤ 0 := hjn
          omega
        have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
        have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hnpos_nat)]
          exact_mod_cast hjn
        linarith
      · intro j hj
        exact ramanujanQTerm_factor_le_exp hk hj
    _ = Real.exp (∑ j ∈ Finset.range k, -(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [Finset.sum_neg_distrib]

lemma ramanujanQTerm_le_exp_quadratic {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ))) := by
  have hsum :
      (∑ j ∈ Finset.range k, (((j : ℝ) + 1) / (n : ℝ))) =
        ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  simpa [Nat.cast_add, hsum] using ramanujanQTerm_le_exp_sum (n := n) (k := k) hk

lemma ramanujanQTerm_le_one {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤ 1 := by
  have h := ramanujanQTerm_le_exp_sum (n := n) (k := k) hk
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    by_cases hn : n = 0
    · subst hn
      simp
    exact div_nonneg (by positivity) (by positivity)
  have hexp : Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤ 1 := by
    rw [← Real.exp_zero, Real.exp_le_exp]
    linarith
  exact h.trans hexp

lemma prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro _h0 _h1
    simp
  · intro a s ha ih h0 h1
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' : 1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
      exact ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hprod_le_one : ∏ i ∈ s, (1 - f i) ≤ 1 := by
      refine Finset.prod_le_one ?_ ?_
      · intro i hi
        have : f i ≤ 1 := h1 i (Finset.mem_insert_of_mem hi)
        linarith
      · intro i hi
        have : 0 ≤ f i := h0 i (Finset.mem_insert_of_mem hi)
        linarith
    have hfa_nonneg : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    calc
      1 - (f a + ∑ i ∈ s, f i) = 1 - ∑ i ∈ s, f i - f a := by ring
      _ ≤ (∏ i ∈ s, (1 - f i)) - f a := by linarith
      _ ≤ (∏ i ∈ s, (1 - f i)) - f a * (∏ i ∈ s, (1 - f i)) := by
        have hmul : f a * (∏ i ∈ s, (1 - f i)) ≤ f a * 1 :=
          mul_le_mul_of_nonneg_left hprod_le_one hfa_nonneg
        linarith
      _ = (1 - f a) * ∏ i ∈ s, (1 - f i) := by ring

lemma one_sub_sum_le_ramanujanQTerm {n k : ℕ} (hk : k ≤ n) :
    1 - (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ≤
      ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine prod_one_sub_ge_one_sub_sum (Finset.range k)
    (fun j => (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ?_ ?_
  · intro j hj
    by_cases hn : n = 0
    · subst hn
      simp
    exact div_nonneg (by positivity) (by positivity)
  · intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    have hjn : j + 1 ≤ n := hjk.trans hk
    by_cases hn : n = 0
    · subst hn
      have : j + 1 ≤ 0 := hjn
      omega
    have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn

lemma gaussianKernel_antitoneOn {n : ℕ} (hn : 0 < n) (a : ℝ) :
    AntitoneOn (gaussianKernel n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [gaussianKernel, gaussianKernel, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ (n : ℝ)⁻¹ * 2⁻¹ := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul : ((n : ℝ)⁻¹ * 2⁻¹) * x ^ 2 ≤
      ((n : ℝ)⁻¹ * 2⁻¹) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma ramanujanQTerm_le_gaussianKernel {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ramanujanQTerm n k ≤ gaussianKernel n k := by
  have hterm := ramanujanQTerm_le_exp_quadratic (n := n) (k := k) hk
  have hquad :
      -(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) ≤
        -((n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hsquare : (k : ℝ) ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
      nlinarith [hk_nonneg]
    have hdiv : (n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2 ≤
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
      field_simp [hnpos.ne']
      nlinarith
    linarith
  exact hterm.trans (Real.exp_le_exp.mpr hquad)

lemma gaussianKernel_zero (n : ℕ) : gaussianKernel n 0 = 1 := by
  simp [gaussianKernel]

lemma sum_gaussianKernel_range_le_one_add_integral {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x := by
  cases n with
  | zero => omega
  | succ m =>
      have hanti : AntitoneOn (gaussianKernel (m + 1)) (Set.Icc 0 (0 + (m : ℝ))) := by
        exact gaussianKernel_antitoneOn (n := m + 1) (by omega) (0 + (m : ℝ))
      have hsum := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := m) hanti
      calc
        (∑ k ∈ Finset.range (m + 1), gaussianKernel (m + 1) k) =
            (∑ k ∈ Finset.range m, gaussianKernel (m + 1) (k + 1)) + 1 := by
          rw [Finset.sum_range_succ']
          simp [gaussianKernel_zero]
        _ ≤ (∫ x in (0 : ℝ)..(0 + (m : ℝ)), gaussianKernel (m + 1) x) + 1 := by
          simpa using add_le_add_right hsum 1
        _ = 1 + ∫ x in (0 : ℝ)..((m + 1 - 1 : ℕ) : ℝ), gaussianKernel (m + 1) x := by
          simp [add_comm]

lemma integral_gaussianKernel_Ioc_le_Ioi {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
  have hb : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hint : MeasureTheory.IntegrableOn (gaussianKernel n) (Set.Ioi (0 : ℝ)) := by
    simpa [gaussianKernel] using
      (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (n : ℝ)⁻¹ * 2⁻¹)).2 (by positivity)
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] gaussianKernel n := by
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  have hsubset : Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ) ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    exact Eventually.of_forall fun x hx => hx.1
  have hset :
      (∫ x in Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
        ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x :=
    MeasureTheory.setIntegral_mono_set (s := Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ))
      (t := Set.Ioi (0 : ℝ)) hint hnonneg hsubset
  have hle : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  simpa [intervalIntegral.integral_of_le hle] using hset

lemma integral_gaussianKernel_Ioi {n : ℕ} (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x) =
      Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  simpa [gaussianKernel] using integral_gaussian_Ioi (b := (n : ℝ)⁻¹ * 2⁻¹)

lemma gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hnpos : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnpos]

lemma sqrt_pi_mul_nat_div_two_le_two_sqrt (n : ℕ) :
    Real.sqrt (Real.pi * (n : ℝ) / 2) ≤ 2 * Real.sqrt (n : ℝ) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  nlinarith [Real.sq_sqrt hnnonneg, Real.pi_le_four]

end
end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

lemma permSingleCycle_iff_isCycle_support_full_of_two_le {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    PermSingleCycle σ ↔ σ.IsCycle ∧ σ.support.card = Fintype.card α := by
  constructor
  · intro hσ
    have hmove : ∀ x : α, σ x ≠ x := by
      intro x hxfix
      rcases Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) x with ⟨y, hy⟩
      rcases hσ x y with ⟨m, hm⟩
      have hfixed : σ^[m] x = x := Function.iterate_fixed hxfix m
      exact hy (hm.symm.trans hfixed)
    have hsupp : σ.support = Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support, hmove x]
    refine ⟨?_, by rw [hsupp, Finset.card_univ]⟩
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    refine ⟨x, hmove x, ?_⟩
    intro y _hy
    rcases hσ x y with ⟨m, hm⟩
    refine ⟨(m : ℤ), ?_⟩
    have hpow : (σ ^ m) x = y := by
      change (⇑(σ ^ m)) x = y
      rw [Equiv.Perm.coe_pow]
      exact hm
    simpa [zpow_natCast] using hpow
  · rintro ⟨hcycle, hsupp_card⟩ x y
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hsupp_card
    have hx : σ x ≠ x := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    have hy : σ y ≠ y := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    rcases (hcycle.sameCycle hx hy).exists_nat_pow_eq with ⟨m, hm⟩
    have hiter : σ^[m] x = y := by
      change (⇑σ)^[m] x = y
      rw [← Equiv.Perm.coe_pow]
      exact hm
    exact ⟨m, hiter⟩

lemma cycleType_singleton_full_iff_permSingleCycle {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    σ.cycleType = ({Fintype.card α} : Multiset ℕ) ↔ PermSingleCycle σ := by
  constructor
  · intro htype
    have hcycle : σ.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [htype]
      simp
    have hsupp : σ.support.card = Fintype.card α := by
      have hsum := Equiv.Perm.sum_cycleType σ
      rw [htype] at hsum
      simpa using hsum.symm
    exact (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mpr
      ⟨hcycle, hsupp⟩
  · intro hsingle
    rcases (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mp hsingle with
      ⟨hcycle, hsupp⟩
    rw [hcycle.cycleType, hsupp]

theorem card_permSingleCycle_of_two_le {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  have hsub :
      Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
        ({g | g.cycleType = ({Fintype.card α} : Multiset ℕ)} :
          Finset (Equiv.Perm α)).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_full_iff_permSingleCycle (σ := g) hα]
  rw [hsub]
  rw [Equiv.Perm.card_of_cycleType_singleton hα (le_rfl : Fintype.card α ≤ Fintype.card α)]
  simp

theorem card_permSingleCycle_of_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    (hα : Fintype.card α ≤ 1) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} = 1 := by
  classical
  have hsub : ∀ x y : α, x = y := Fintype.card_le_one_iff.mp hα
  refine Fintype.card_eq_one_iff.mpr ⟨⟨1, ?_⟩, ?_⟩
  · intro x y
    exact ⟨0, hsub x y⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro x
    exact hsub _ _

theorem card_permSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  by_cases hα : 2 ≤ Fintype.card α
  · exact card_permSingleCycle_of_two_le hα
  · have hle : Fintype.card α ≤ 1 := by omega
    have hsmall : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
    rw [card_permSingleCycle_of_card_le_one hle]
    rcases hsmall with h0 | h1
    · simp [h0]
    · simp [h1]

lemma ramanujanQTerm_eq_descFactorial_div {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    RamanujanQNS.ramanujanQTerm n k =
      ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
  classical
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  let qFactor : ℕ → ℝ :=
    fun j : ℕ => (1 : ℝ) - (((j + 1 : ℕ) : ℝ) / (n : ℝ))
  let dFactor : ℕ → ℝ :=
    fun j : ℕ => ((n - 1 - j : ℕ) : ℝ) / (n : ℝ)
  have hfactor (j : ℕ) (hj : j ∈ Finset.range k) :
      qFactor j = dFactor j := by
    have hjk : j < k := Finset.mem_range.mp hj
    have hle : j + 1 ≤ n := by omega
    have hsub : n - (j + 1) = n - 1 - j := by omega
    dsimp [qFactor, dFactor]
    rw [← hsub]
    rw [Nat.cast_sub hle]
    field_simp [hnne]
  unfold RamanujanQNS.ramanujanQTerm
  change (∏ j ∈ Finset.range k, qFactor j) =
    ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k
  calc
    (∏ j ∈ Finset.range k, qFactor j) =
        ∏ j ∈ Finset.range k, dFactor j := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact hfactor j hj
    _ =
        ∏ j ∈ Finset.range k, (((n - 1 - j : ℕ) : ℝ) / (n : ℝ)) := by
          rfl
    _ =
        (∏ j ∈ Finset.range k, ((n - 1 - j : ℕ) : ℝ)) /
          ∏ _j ∈ Finset.range k, (n : ℝ) := by
          rw [Finset.prod_div_distrib]
    _ =
        ((∏ j ∈ Finset.range k, (n - 1 - j : ℕ)) : ℝ) / (n : ℝ) ^ k := by
          rw [Finset.prod_const]
          simp only [Finset.card_range]
    _ = ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
          rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]

end
end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

/-!
# Components of random mappings

The component count is defined as the number of nonempty single-cycle
restrictions of the permutation induced by a mapping on its periodic core.  A
candidate cycle `C` of a map is counted exactly when the ambient map restricts
to a cyclic permutation on `C`; this is equivalent to being one cycle of the
periodic-core permutation.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

lemma componentCount_eq_mapCycle_card {n : ℕ} (f : Fin n → Fin n) :
    componentCount f = Fintype.card (MapCycleOfMap f) := by
  exact @Fintype.card_congr (CoreCycleOfMap f) (MapCycleOfMap f)
    (coreCycleOfMapFintype f) inferInstance (coreCycleMapCycleEquiv f)

lemma card_mapsRespectingCandidate {n : ℕ} (A : CandidateCycle n) :
    Fintype.card (MapsRespectingCandidate A) =
      n ^ (n - candidateCard A) := by
  classical
  calc
    Fintype.card (MapsRespectingCandidate A) =
        Fintype.card ({x : Fin n // x ∉ candidateSupport A} → Fin n) := by
          exact Fintype.card_congr (mapsRespectingCandidateEquiv A)
    _ = n ^ Fintype.card {x : Fin n // x ∉ candidateSupport A} := by
          rw [Fintype.card_fun, Fintype.card_fin]
    _ = n ^ (n - candidateCard A) := by
          congr 1
          change Fintype.card {x : Fin n // x ∉ candidateSupport A} =
            n - (candidateSupport A).card
          rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ candidateSupport A)]
          simp [Fintype.card_fin]

lemma sum_componentCount_eq_candidate_maps (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
  classical
  calc
    (∑ f : Fin n → Fin n, componentCount f) =
        ∑ f : Fin n → Fin n, Fintype.card (MapCycleOfMap f) := by
          refine Finset.sum_congr rfl ?_
          intro f _
          exact componentCount_eq_mapCycle_card f
    _ = Fintype.card (Sigma fun f : Fin n → Fin n => MapCycleOfMap f) := by
          exact Fintype.card_sigma.symm
    _ = Fintype.card (Sigma fun A : CandidateCycle n => MapsRespectingCandidate A) := by
          exact Fintype.card_congr (mapCycleSwapEquiv n)
    _ = ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
          exact Fintype.card_sigma

lemma candidate_maps_sum_by_card (n : ℕ) :
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  classical
  calc
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
        ∑ A : CandidateCycle n, n ^ (n - candidateCard A) := by
          refine Finset.sum_congr rfl ?_
          intro A _
          exact card_mapsRespectingCandidate A
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          ∑ σ : {σ : Equiv.Perm C.1 // PermSingleCycle σ},
            n ^ (n - C.1.card) := by
          rw [Fintype.sum_sigma]
          rfl
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          (C.1.card - 1).factorial * n ^ (n - C.1.card) := by
          refine Finset.sum_congr rfl ?_
          intro C _
          simp [card_permSingleCycle, Fintype.card_coe, mul_comm]
    _ =
        ∑ i ∈ Finset.range n,
          Nat.choose n (i + 1) *
            ((i + 1 - 1).factorial * n ^ (n - (i + 1))) := by
          simpa [Fintype.card_fin] using
            (AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete.sum_nonempty_finsets_by_card
              (β := Fin n)
              (f := fun k : ℕ => (k - 1).factorial * n ^ (n - k)))
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
          simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc, mul_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun k : ℕ =>
                Nat.choose n k * (k - 1).factorial * n ^ (n - k))
              1 (n + 1)).symm

theorem sum_componentCount_eq (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  rw [sum_componentCount_eq_candidate_maps n, candidate_maps_sum_by_card n]

lemma descFactorial_eq_k_mul_choose_mul_pred_factorial {n k : ℕ} (hk : 0 < k) :
    n.descFactorial k = k * (Nat.choose n k * (k - 1).factorial) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.factorial_succ]
  ring

lemma expectation_term_eq_desc {n k : ℕ} (hn : 0 < n)
    (hk : k ∈ Finset.Icc 1 n) :
    (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
        (n : ℝ) ^ n) =
      (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ) ^ k) := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hkpos
  have htail_ne : (n : ℝ) ^ (n - k) ≠ 0 := pow_ne_zero _ hnne
  have hpowk_ne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ hnne
  have hsplit : n = (n - k) + k := by omega
  have hpow_split : (n : ℝ) ^ n = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ ((n - k) + k) := by
        exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
      _ = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
        rw [pow_add]
  have hdesc :
      (n.descFactorial k : ℝ) =
        (k : ℝ) * ((Nat.choose n k * (k - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast descFactorial_eq_k_mul_choose_mul_pred_factorial (n := n) (k := k) hkpos
  rw [hpow_split, hdesc]
  push_cast
  field_simp [hkne, htail_ne, hpowk_ne]

/-- Exact expected number of components in a uniform random mapping on `n` labels. -/
theorem expected_components_eq {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n
      = ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
  classical
  have hsum_nat := sum_componentCount_eq n
  have hsum_real :
      (∑ f : Fin n → Fin n, (componentCount f : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  calc
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n =
        (∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ)) /
            (n : ℝ)^n := by
          rw [hsum_real]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
            (n : ℝ)^n) := by
          rw [Finset.sum_div]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact expectation_term_eq_desc hn hk

lemma descFactorial_succ_eq_mul_pred {n i : ℕ} (hi : i < n) :
    n.descFactorial (i + 1) = n * (n - 1).descFactorial i := by
  have h := Nat.succ_descFactorial_succ (n - 1) i
  have hnpos : 0 < n := by omega
  have hnsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  simpa [hnsucc, Nat.add_comm] using h

lemma component_formula_term_eq_ramanujan {n i : ℕ} (hn : 0 < n)
    (hi : i ∈ Finset.range n) :
    (n.descFactorial (i + 1) : ℝ) /
        (((i + 1 : ℕ) : ℝ) * (n : ℝ) ^ (i + 1)) =
      ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
  have hilt : i < n := Finset.mem_range.mp hi
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hi1ne : (((i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpowi_ne : (n : ℝ) ^ i ≠ 0 := pow_ne_zero _ hnne
  rw [ramanujanQTerm_eq_descFactorial_div hn hilt]
  rw [descFactorial_succ_eq_mul_pred (n := n) (i := i) hilt]
  push_cast
  rw [pow_succ]
  field_simp [hnne, hi1ne, hpowi_ne]

theorem componentExpectationFormula_eq_weightedRamanujan {n : ℕ} (hn : 0 < n) :
    componentExpectationFormula n = weightedRamanujanComponents n := by
  classical
  unfold componentExpectationFormula weightedRamanujanComponents
  have hreindex :
      (∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k)) =
        ∑ i ∈ Finset.range n,
          (n.descFactorial (i + 1) : ℝ) /
            (((i + 1 : ℕ) : ℝ) * (n : ℝ)^(i + 1)) := by
    simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      (Finset.sum_Ico_eq_sum_range
        (f := fun k : ℕ =>
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k))
        1 (n + 1))
  rw [hreindex]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact component_formula_term_eq_ramanujan hn hi

lemma harmonic_real_eq_sum_inv (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)⁻¹) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

end
end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

/-!
# Sharp logarithmic asymptotic for mapping components

The expected number of connected components in a uniform random mapping on
`n` labels is asymptotic to `(1 / 2) log n`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

namespace Sharp

-- The finite-sum comparisons below combine several imported analytic bounds;
-- a larger heartbeat budget avoids brittleness in the final asymptotic squeeze.
set_option maxHeartbeats 800000

private lemma componentLogScale_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / 2) atTop atTop := by
  exact Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma gaussianKernel_sum_le_one_add_sqrt {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  calc
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
        1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x :=
      sum_gaussianKernel_range_le_one_add_integral hn
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
      exact add_le_add (le_refl 1) (integral_gaussianKernel_Ioc_le_Ioi hn)
    _ = 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
      rw [integral_gaussianKernel_Ioi hn]
    _ = 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
      rw [gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two hn]

private lemma gaussianKernel_sum_div_nat_sqrt_succ_le_three {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 3 := by
  have hden_pos : (0 : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_le_den :
      Real.sqrt (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.real_sqrt_le_nat_sqrt_succ (a := n)
  have hsum := gaussianKernel_sum_le_one_add_sqrt (n := n) hn
  have htail :
      (∑ k ∈ Finset.range n, gaussianKernel n k) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
        (1 + Real.sqrt (Real.pi * (n : ℝ) / 2)) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right hsum hden_pos.le
  have hone : (1 : ℝ) / (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one₀ hden_pos]
    exact_mod_cast Nat.succ_pos (Nat.sqrt n)
  have hgauss :
      Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 2 := by
    have hnum := sqrt_pi_mul_nat_div_two_le_two_sqrt n
    calc
      Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
        (2 * Real.sqrt (n : ℝ)) / (((Nat.sqrt n + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right hnum hden_pos.le
      _ ≤ (2 * (((Nat.sqrt n + 1 : ℕ) : ℝ))) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt_le_den (by norm_num : (0 : ℝ) ≤ 2))
              hden_pos.le
      _ = 2 := by
        field_simp [hden_pos.ne']
  calc
    (∑ k ∈ Finset.range n, gaussianKernel n k) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
      (1 + Real.sqrt (Real.pi * (n : ℝ) / 2)) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) := htail
    _ = 1 / (((Nat.sqrt n + 1 : ℕ) : ℝ)) +
        Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 1 + 2 := add_le_add hone hgauss
    _ = 3 := by norm_num

private lemma weightedRamanujanComponents_tail_le_three {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ (Finset.range n).filter fun i => Nat.sqrt n ≤ i,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤ 3 := by
  classical
  let K : ℕ := Nat.sqrt n
  have htail_to_gauss :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_range : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
    have hKi : K ≤ i := (Finset.mem_filter.mp hi).2
    have hterm_nonneg : 0 ≤ ramanujanQTerm n i :=
      ramanujanQTerm_nonneg (n := n) (k := i) (Nat.le_of_lt (Finset.mem_range.mp hi_range))
    have hterm_gauss : ramanujanQTerm n i ≤ gaussianKernel n i :=
      ramanujanQTerm_le_gaussianKernel hn (Nat.le_of_lt (Finset.mem_range.mp hi_range))
    have hden_i_pos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hden_K_pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    have hden_le : ((K + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hKi
    calc
      ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) ≤
          gaussianKernel n i / (((i + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hterm_gauss hden_i_pos.le
      _ ≤ gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
        have hg_nonneg : 0 ≤ gaussianKernel n i := (Real.exp_pos _).le
        exact div_le_div_of_nonneg_left hg_nonneg hden_K_pos hden_le
  have hfilter_to_full :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          gaussianKernel n i / (((K + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; exact (Finset.mem_filter.mp hi).1) ?_
    intro i hi_range hi_not
    exact div_nonneg (Real.exp_pos _).le (by positivity)
  have hfull :
      (∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ))) =
        (∑ i ∈ Finset.range n, gaussianKernel n i) / (((K + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_div]
  calc
    (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
      ∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
        gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := htail_to_gauss
    _ ≤ ∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := hfilter_to_full
    _ = (∑ i ∈ Finset.range n, gaussianKernel n i) / (((K + 1 : ℕ) : ℝ)) := hfull
    _ ≤ 3 := by
      simpa [K] using gaussianKernel_sum_div_nat_sqrt_succ_le_three (n := n) hn

private lemma weightedRamanujanComponents_le_harmonic_sqrt_add_three {n : ℕ} (hn : 0 < n) :
    weightedRamanujanComponents n ≤ (harmonic (Nat.sqrt n) : ℝ) + 3 := by
  classical
  let K : ℕ := Nat.sqrt n
  have hsplit :
      weightedRamanujanComponents n =
        (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) +
        (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) := by
    unfold weightedRamanujanComponents
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range n)
      (p := fun i => i < K)
      (f := fun i => ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)))]
    refine congrArg₂ HAdd.hAdd ?_ ?_
    · rfl
    · refine Finset.sum_congr ?_ ?_
      · ext i
        simp [not_lt]
      · intro i hi
        rfl
  have hhead :
      (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        (harmonic K : ℝ) := by
    calc
      (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ (Finset.range n).filter fun i => i < K,
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_range : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
          have hle := ramanujanQTerm_le_one (n := n) (k := i)
            (Nat.le_of_lt (Finset.mem_range.mp hi_range))
          have hden : 0 ≤ (((i + 1 : ℕ) : ℝ)) := by positivity
          simpa [one_div] using div_le_div_of_nonneg_right hle hden
      _ ≤ ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro i hi
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i hi _hi_not
            positivity
      _ = (harmonic K : ℝ) := (harmonic_real_eq_sum_inv K).symm
  have htail :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤ 3 := by
    simpa [K] using weightedRamanujanComponents_tail_le_three (n := n) hn
  rw [hsplit]
  exact add_le_add hhead htail

private lemma harmonic_nat_sqrt_le_log_half_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic (Nat.sqrt n) : ℝ) ≤ Real.log (n : ℝ) / 2 + 1 := by
  have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hH := harmonic_le_one_add_log (Nat.sqrt n)
  have hlog_le :
      Real.log (Nat.sqrt n : ℝ) ≤ Real.log (Real.sqrt (n : ℝ)) := by
    exact Real.log_le_log (by exact_mod_cast hspos) Real.nat_sqrt_le_real_sqrt
  have hlogsqrt :
      Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 := by
    rw [Real.log_sqrt (by positivity : 0 ≤ (n : ℝ))]
  calc
    (harmonic (Nat.sqrt n) : ℝ) ≤ 1 + Real.log (Nat.sqrt n : ℝ) := hH
    _ ≤ 1 + Real.log (Real.sqrt (n : ℝ)) := by linarith
    _ = Real.log (n : ℝ) / 2 + 1 := by rw [hlogsqrt]; ring

private lemma weightedRamanujanComponents_le_log_half_add_four {n : ℕ} (hn : 0 < n) :
    weightedRamanujanComponents n ≤ Real.log (n : ℝ) / 2 + 4 := by
  have h := weightedRamanujanComponents_le_harmonic_sqrt_add_three (n := n) hn
  have hH := harmonic_nat_sqrt_le_log_half_add_one (n := n) hn
  linarith

private lemma exists_nat_one_sub_inv_two_sq_gt {a : ℝ} (ha : a < 1) :
    ∃ L : ℕ, 0 < L ∧ a < 1 - 1 / (2 * (L : ℝ) ^ 2) := by
  let δ : ℝ := 1 - a
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (max (1 : ℝ) (1 / (2 * δ)))
  have hL_one : (1 : ℝ) < (L : ℝ) := (max_lt_iff.mp hL).1
  have hL_bound : 1 / (2 * δ) < (L : ℝ) := (max_lt_iff.mp hL).2
  have hLpos : 0 < L := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hL_one)
  have hL_le_sq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by
    nlinarith [le_of_lt hL_one]
  have hbound_sq : 1 / (2 * δ) < (L : ℝ) ^ 2 :=
    hL_bound.trans_le hL_le_sq
  have hmain : (1 : ℝ) < 2 * δ * (L : ℝ) ^ 2 := by
    have htmp := mul_lt_mul_of_pos_left hbound_sq
      (by positivity : (0 : ℝ) < 2 * δ)
    have hleft : (2 * δ) * (1 / (2 * δ)) = (1 : ℝ) := by
      field_simp [hδ.ne']
    rw [hleft] at htmp
    nlinarith
  have hinv : 1 / (2 * (L : ℝ) ^ 2) < δ := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
    nlinarith
  refine ⟨L, hLpos, ?_⟩
  dsimp [δ] at hinv
  linarith

private lemma nat_sqrt_div_add_one_ge_real_sqrt_div {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    Real.sqrt (n : ℝ) / (2 * (L : ℝ)) ≤
      ((Nat.sqrt n / L + 1 : ℕ) : ℝ) := by
  let s : ℕ := Nat.sqrt n
  have hspos : 0 < s := by
    dsimp [s]
    exact Nat.sqrt_pos.mpr hn
  have hs_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hspos
  have hsqrt_le_two_s :
      Real.sqrt (n : ℝ) ≤ 2 * (s : ℝ) := by
    have hsqrtle : Real.sqrt (n : ℝ) ≤ (s : ℝ) + 1 := by
      simpa [s, Nat.cast_add, Nat.cast_one] using
        Real.real_sqrt_le_nat_sqrt_succ (a := n)
    have htwo : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by nlinarith
    exact hsqrtle.trans htwo
  have hLpos_real : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hdivlt_nat : s < (s / L + 1) * L := by
    have hlt : s / L < s / L + 1 := Nat.lt_succ_self _
    exact (Nat.div_lt_iff_lt_mul hL).mp hlt
  have hs_div_le : (s : ℝ) / (L : ℝ) ≤ ((s / L + 1 : ℕ) : ℝ) := by
    have hcast : (s : ℝ) < ((s / L + 1 : ℕ) : ℝ) * (L : ℝ) := by
      exact_mod_cast hdivlt_nat
    rw [div_le_iff₀ hLpos_real]
    exact le_of_lt (by simpa [mul_comm] using hcast)
  calc
    Real.sqrt (n : ℝ) / (2 * (L : ℝ)) ≤
        (2 * (s : ℝ)) / (2 * (L : ℝ)) := by
      exact div_le_div_of_nonneg_right hsqrt_le_two_s (by positivity)
    _ = (s : ℝ) / (L : ℝ) := by field_simp [hLpos_real.ne']
    _ ≤ ((s / L + 1 : ℕ) : ℝ) := hs_div_le

private lemma log_half_sub_log_two_mul_le_log_nat_sqrt_div_add_one
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) ≤
      Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hleft_pos : 0 < Real.sqrt (n : ℝ) / (2 * (L : ℝ)) := by
    positivity
  have hle := nat_sqrt_div_add_one_ge_real_sqrt_div (L := L) (n := n) hL hn
  have hlog :=
    Real.log_le_log hleft_pos hle
  have hlog_left :
      Real.log (Real.sqrt (n : ℝ) / (2 * (L : ℝ))) =
        Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) := by
    rw [Real.log_div (by positivity : Real.sqrt (n : ℝ) ≠ 0)
      (by positivity : (2 * (L : ℝ)) ≠ 0)]
    rw [Real.log_sqrt (by positivity : 0 ≤ (n : ℝ))]
  simpa [hlog_left] using hlog

private lemma ramanujanQTerm_ge_one_sub_inv_two_sq_of_lt_sqrt_div
    {L n i : ℕ} (hL : 0 < L) (hn : 0 < n) (hi : i < Nat.sqrt n / L) :
    (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) ≤ ramanujanQTerm n i := by
  let K : ℕ := Nat.sqrt n / L
  have hiK_succ : i + 1 ≤ K := Nat.succ_le_of_lt hi
  have hLK_le_sqrt : L * (i + 1) ≤ Nat.sqrt n := by
    have hmul : L * (i + 1) ≤ L * K := Nat.mul_le_mul_left L hiK_succ
    have hLK : L * K ≤ Nat.sqrt n := by
      dsimp [K]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (Nat.sqrt n) L
    exact hmul.trans hLK
  have hLi_le_sqrt : L * i ≤ Nat.sqrt n := by
    exact (Nat.mul_le_mul_left L (Nat.le_succ i)).trans hLK_le_sqrt
  have hmul_nat : (L * i) * (L * (i + 1)) ≤ n := by
    calc
      (L * i) * (L * (i + 1)) ≤ Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_le_mul hLi_le_sqrt hLK_le_sqrt
      _ ≤ n := Nat.sqrt_le n
  have hi_le_n : i ≤ n := by
    calc
      i ≤ Nat.sqrt n := by
        exact (le_of_lt hi).trans (Nat.div_le_self (Nat.sqrt n) L)
      _ ≤ n := Nat.sqrt_le_self n
  have hsum := one_sub_sum_le_ramanujanQTerm (n := n) (k := i) hi_le_n
  have hquad :
      ((i : ℝ) * ((i : ℝ) + 1) / 2) / (n : ℝ) ≤
        1 / (2 * (L : ℝ) ^ 2) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hmul_real :
        ((L : ℝ) * (i : ℝ)) * ((L : ℝ) * ((i + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast hmul_nat
    rw [Nat.cast_add, Nat.cast_one] at hmul_real
    field_simp [hnpos.ne', hLpos.ne']
    nlinarith [hmul_real]
  have hsum_eval :
      (∑ j ∈ Finset.range i, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
        (((i : ℝ) * ((i : ℝ) + 1) / 2) / (n : ℝ)) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div i n
  calc
    (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) ≤
        1 - (∑ j ∈ Finset.range i, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [hsum_eval]
      linarith
    _ ≤ ramanujanQTerm n i := hsum

private lemma weightedRamanujanComponents_lower_fixed
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (harmonic (Nat.sqrt n / L) : ℝ) ≤
      weightedRamanujanComponents n := by
  classical
  let K : ℕ := Nat.sqrt n / L
  have hK_le_n : K ≤ n := by
    dsimp [K]
    exact (Nat.div_le_self (Nat.sqrt n) L).trans (Nat.sqrt_le_self n)
  have hsubset : Finset.range K ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hK_le_n)
  have halpha_nonneg : 0 ≤ (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hLsq_ge : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL]
    have hinv_le : 1 / (2 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
      nlinarith
    linarith
  calc
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (harmonic K : ℝ) =
      ∑ i ∈ Finset.range K,
        ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) / (((i + 1 : ℕ) : ℝ)) := by
        rw [harmonic_real_eq_sum_inv, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [div_eq_mul_inv]
        ring
    _ ≤ ∑ i ∈ Finset.range K,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hterm := ramanujanQTerm_ge_one_sub_inv_two_sq_of_lt_sqrt_div
          (L := L) (n := n) (i := i) hL hn (Finset.mem_range.mp hi)
        exact div_le_div_of_nonneg_right hterm (by positivity)
    _ ≤ ∑ i ∈ Finset.range n,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro i hi _hi_not
        have hnonneg := ramanujanQTerm_nonneg (n := n) (k := i)
          (Nat.le_of_lt (Finset.mem_range.mp hi))
        exact div_nonneg hnonneg (by positivity)
    _ = weightedRamanujanComponents n := by
        simp [weightedRamanujanComponents]

private lemma weightedRamanujanComponents_lower_log_fixed
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ))) ≤
      weightedRamanujanComponents n := by
  let α : ℝ := (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hLsq_ge : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL]
    have hinv_le : 1 / (2 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
      nlinarith
    linarith
  have hlog :
      Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) ≤
        Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) :=
    log_half_sub_log_two_mul_le_log_nat_sqrt_div_add_one (L := L) (n := n) hL hn
  have hH :
      Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) ≤
        (harmonic (Nat.sqrt n / L) : ℝ) := by
    simpa using log_add_one_le_harmonic (Nat.sqrt n / L)
  have hfixed := weightedRamanujanComponents_lower_fixed (L := L) (n := n) hL hn
  calc
    α * (Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ))) ≤
        α * (harmonic (Nat.sqrt n / L) : ℝ) :=
      mul_le_mul_of_nonneg_left (hlog.trans hH) hα_nonneg
    _ ≤ weightedRamanujanComponents n := by
      simpa [α] using hfixed

private lemma eventually_weighted_ratio_le_of_gt_one {a : ℝ} (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop,
      weightedRamanujanComponents n / (Real.log (n : ℝ) / 2) < a := by
  let g : ℕ → ℝ := fun n => Real.log (n : ℝ) / 2
  have hg : Tendsto g atTop atTop := componentLogScale_tendsto_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (4 : ℝ) / g n < a - 1 :=
    (Filter.Tendsto.const_div_atTop hg (4 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr ha))
  filter_upwards [hsmall, hg.eventually_gt_atTop (0 : ℝ),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hgpos hn
  have hnpos : 0 < n := by omega
  have hupper := weightedRamanujanComponents_le_log_half_add_four (n := n) hnpos
  have hratio :
      weightedRamanujanComponents n / g n ≤ 1 + 4 / g n := by
    calc
      weightedRamanujanComponents n / g n ≤ (g n + 4) / g n :=
        div_le_div_of_nonneg_right (by simpa [g] using hupper) hgpos.le
      _ = 1 + 4 / g n := by
        field_simp [hgpos.ne']
  change weightedRamanujanComponents n / g n < a
  linarith

private lemma eventually_weighted_ratio_ge_of_lt_one {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in atTop,
      a < weightedRamanujanComponents n / (Real.log (n : ℝ) / 2) := by
  obtain ⟨L, hLpos, hLa⟩ := exists_nat_one_sub_inv_two_sq_gt ha
  let α : ℝ := (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)
  let C : ℝ := Real.log (2 * (L : ℝ))
  have hαa : a < α := by simpa [α] using hLa
  have hgap : 0 < α - a := sub_pos.mpr hαa
  let g : ℕ → ℝ := fun n => Real.log (n : ℝ) / 2
  have hg : Tendsto g atTop atTop := componentLogScale_tendsto_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (α * C) / g n < α - a :=
    (Filter.Tendsto.const_div_atTop hg (α * C)).eventually (gt_mem_nhds hgap)
  filter_upwards [hsmall, hg.eventually_gt_atTop (0 : ℝ),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hgpos hn
  have hnpos : 0 < n := by omega
  have hlower := weightedRamanujanComponents_lower_log_fixed
    (L := L) (n := n) hLpos hnpos
  have hratio_lower :
      α - (α * C) / g n ≤ weightedRamanujanComponents n / g n := by
    calc
      α - (α * C) / g n =
          (α * (g n - C)) / g n := by
            field_simp [hgpos.ne']
      _ ≤ weightedRamanujanComponents n / g n :=
        div_le_div_of_nonneg_right (by simpa [α, C, g] using hlower) hgpos.le
  change a < weightedRamanujanComponents n / g n
  linarith

theorem weightedRamanujanComponents_tendsto_ratio_one :
    Tendsto
      (fun n : ℕ => weightedRamanujanComponents n / (Real.log (n : ℝ) / 2))
      atTop (𝓝 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact eventually_weighted_ratio_ge_of_lt_one ha
  · intro a ha
    exact eventually_weighted_ratio_le_of_gt_one ha

theorem weightedRamanujanComponents_isEquivalent :
    (fun n : ℕ => weightedRamanujanComponents n) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  exact Asymptotics.isEquivalent_of_tendsto_one weightedRamanujanComponents_tendsto_ratio_one

theorem componentExpectationFormula_isEquivalent :
    (fun n : ℕ => componentExpectationFormula n) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  refine weightedRamanujanComponents_isEquivalent.congr_left ?_
  exact eventually_atTop.2 ⟨1, fun n hn => by
    exact (componentExpectationFormula_eq_weightedRamanujan (n := n) (by omega)).symm⟩

end Sharp
end
end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS
set_option maxHeartbeats 800000
theorem solution :
    (fun n : ℕ => (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  refine componentExpectationFormula_isEquivalent.congr_left ?_
  exact eventually_atTop.2 ⟨1, fun n hn => by
    exact (expected_components_eq (n := n) (by omega)).symm⟩
