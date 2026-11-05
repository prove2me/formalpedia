-- Prove2me | solution 2 for MarkovMixing.evolving_sets_mixing
-- status  : ACCEPTED   (prove)
-- author  : @steven
-- created : 2026-08-22T22:30:12.191388+00:00
-- url     : https://prove2.me/submissions/71cacc0d-1b21-4f9e-89f0-c85f283adb12

import Theorems.Thm_MarkovMixing_evolving_sets_tv_decay
import Theorems.Thm_MarkovMixing_bottleneckStar_pos
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators
open MarkovMixing

namespace MarkovMixingXGoal

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [h]
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

private lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

private lemma stationary_pos {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ x : V, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    linarith [hπ.1.2]
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have hsingle : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  nlinarith [mul_pos hy ht]

private lemma finite_iInf_pos [Nonempty V] (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    0 < ⨅ x, f x := by
  classical
  let vals : Finset ℝ := Finset.univ.image f
  have hvals : vals.Nonempty := by
    let x : V := Classical.choice inferInstance
    exact ⟨f x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  let m := vals.min' hvals
  have hm_mem : m ∈ vals := Finset.min'_mem vals hvals
  obtain ⟨xmin, -, hxmin⟩ := Finset.mem_image.mp hm_mem
  have hmpos : 0 < m := by simpa [hxmin] using hf xmin
  have hmle : ∀ x : V, m ≤ f x := by
    intro x
    exact Finset.min'_le vals (f x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨x, rfl⟩; exact (hf x).le⟩
  have heq : (⨅ x, f x) = m := by
    apply le_antisymm
    · have hle := ciInf_le hbdd xmin
      linarith [hxmin]
    · exact le_ciInf hmle
  rw [heq]
  exact hmpos

private lemma bottleneck_le_one [Nonempty V] (hV : 2 ≤ Fintype.card V)
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) : bottleneckStar P π ≤ 1 := by
  classical
  have hpos := stationary_pos hP hirr hπ
  have hedge : ∀ x y : V, 0 ≤ edgeMeasure P π x y :=
    fun x y => mul_nonneg (hpos x).le (hP.1 x y)
  have hbdd : BddBelow (Set.range fun S : {S : Finset V //
      S.Nonempty ∧ ∑ x ∈ S, π x ≤ (2 : ℝ)⁻¹} => bottleneckRatio P π S.1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hedge x y)
      (Finset.sum_nonneg fun x _ => (hpos x).le)
  obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ (2 : ℝ)⁻¹ := by
    by_contra hcon
    push_neg at hcon
    have hcard : 1 < Fintype.card V := by omega
    obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
    have hpairsum : π x + π y ≤ ∑ z, π z := by
      calc
        π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := (Finset.sum_pair hxy).symm
        _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun i _ _ => (hpos i).le)
    linarith [hcon x, hcon y, hπ.1.2]
  let S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ (2 : ℝ)⁻¹} :=
    ⟨{x}, Finset.singleton_nonempty x, by simpa using hx⟩
  refine le_trans (ciInf_le hbdd S) ?_
  change bottleneckRatio P π {x} ≤ 1
  have hden : 0 < ∑ z ∈ ({x} : Finset V), π z := by simp [hpos x]
  rw [bottleneckRatio, div_le_one hden]
  simp only [Finset.sum_singleton]
  calc
    ∑ y ∈ ({x} : Finset V)ᶜ, edgeMeasure P π x y
        ≤ ∑ y : V, edgeMeasure P π x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => hedge x y)
    _ = π x := by simp [edgeMeasure, ← Finset.mul_sum, hP.2 x]

private lemma singleton_mixing_zero [Nonempty V] (hcard : Fintype.card V ≤ 1)
    (P : Matrix V V ℝ) (π : V → ℝ) (hπ : IsStationary P π) (ε : ℝ) (hε : 0 < ε) :
    mixingTime P π ε = 0 := by
  classical
  letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hcard
  let x : V := Classical.choice inferInstance
  have hsum : ∑ y : V, π y = π x := by
    calc
      ∑ y : V, π y = ∑ _y : V, π x := Finset.sum_congr rfl fun y _ => by rw [Subsingleton.elim y x]
      _ = π x := by simp [Fintype.card_eq_one_iff.mpr ⟨x, fun y => Subsingleton.elim y x⟩]
  have hpix : π x = 1 := by linarith [hπ.1.2, hsum]
  have hpi : π = fun _ => 1 := by
    funext y
    rw [Subsingleton.elim y x, hpix]
  have hrow : ∀ y : V, rowDist P 0 y = π := by
    intro y
    funext z
    rw [hpi]
    simp [rowDist, Matrix.one_apply, Subsingleton.elim y z]
  have hd : distStationary P π 0 = 0 := by
    simp [distStationary, hrow, tvDist]
  apply le_antisymm
  · exact Nat.sInf_le (by simpa [hd] using hε.le)
  · exact Nat.zero_le _

end MarkovMixingXGoal

/-- **Theorem 17.10** (Morris–Peres; LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime P π ε : ℝ) ≤
      ⌈2 / bottleneckStar P π ^ 2 * Real.log (1 / (ε * ⨅ x : V, π x))⌉₊ := by
  classical
  by_cases hcard : 2 ≤ Fintype.card V
  · let p : ℝ := ⨅ x : V, π x
    let φ : ℝ := bottleneckStar P π
    let a : ℝ := φ ^ 2 / 2
    let B : ℝ := 2 / φ ^ 2 * Real.log (1 / (ε * p))
    let n : ℕ := ⌈B⌉₊
    have hpos := MarkovMixingXGoal.stationary_pos hP hirr hπ
    have hp : 0 < p := MarkovMixingXGoal.finite_iInf_pos π hpos
    have hφ : 0 < φ := MarkovMixing.bottleneckStar_pos hcard P hP hirr π hπ
    have hφ1 : φ ≤ 1 := MarkovMixingXGoal.bottleneck_le_one hcard P hP hirr π hπ
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by dsimp [a]; nlinarith
    have hq : 0 < 1 / (ε * p) := one_div_pos.mpr (mul_pos hε hp)
    have hlog : 0 < Real.log (1 / (ε * p)) := by
      rw [Real.log_pos_iff hq.le]
      have hp_le_one : p ≤ 1 := by
        let x : V := Classical.choice inferInstance
        have hip : p ≤ π x := ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact (hpos y).le⟩ x
        have hpix_le : π x ≤ 1 := by
          have hs := Finset.single_le_sum (f := π) (fun y _ => (hpos y).le) (Finset.mem_univ x)
          linarith [hπ.1.2]
        exact hip.trans hpix_le
      have : ε * p < 1 := by nlinarith [hp]
      exact one_lt_one_div (mul_pos hε hp) this
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hnB : B ≤ (n : ℝ) := by exact Nat.le_ceil B
    have hbase0 : 0 ≤ 1 - a := by linarith
    have hbase_exp : 1 - a ≤ Real.exp (-a) := Real.one_sub_le_exp_neg a
    have hpow : (1 - a) ^ n ≤ Real.exp (-a * n) := by
      calc
        (1 - a) ^ n ≤ Real.exp (-a) ^ n := pow_le_pow_left₀ hbase0 hbase_exp n
        _ = Real.exp ((n : ℝ) * (-a)) := (Real.exp_nat_mul (-a) n).symm
        _ = Real.exp (-a * n) := by congr 1 <;> ring
    have haB : a * B = Real.log (1 / (ε * p)) := by
      dsimp [a, B]
      field_simp
    have hexp_le : Real.exp (-a * n) ≤ ε * p := by
      have harg : -a * (n : ℝ) ≤ -Real.log (1 / (ε * p)) := by
        have hmul := mul_le_mul_of_nonneg_left hnB ha0
        rw [haB] at hmul
        nlinarith
      have hlog_inv : -Real.log (1 / (ε * p)) = Real.log (ε * p) := by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt (mul_pos hε hp)), Real.log_one,
          zero_sub, neg_neg]
      calc
        Real.exp (-a * n) ≤ Real.exp (Real.log (ε * p)) :=
          Real.exp_le_exp.mpr (harg.trans_eq hlog_inv)
        _ = ε * p := Real.exp_log (mul_pos hε hp)
    have hdist : distStationary P π n ≤ ε := by
      have hdecay := MarkovMixing.evolving_sets_tv_decay P hP hirr hlazy π hπ n
      change distStationary P π n ≤ 1 / p * (1 - a) ^ n at hdecay
      calc
        distStationary P π n ≤ 1 / p * (1 - a) ^ n := hdecay
        _ ≤ 1 / p * Real.exp (-a * n) := mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hp.le)
        _ ≤ 1 / p * (ε * p) := mul_le_mul_of_nonneg_left hexp_le (one_div_nonneg.mpr hp.le)
        _ = ε := by field_simp
    have hmix : mixingTime P π ε ≤ n := Nat.sInf_le hdist
    change (mixingTime P π ε : ℝ) ≤ (n : ℝ)
    exact_mod_cast hmix
  · have hcard1 : Fintype.card V ≤ 1 := by omega
    have hm0 := MarkovMixingXGoal.singleton_mixing_zero hcard1 P π hπ ε hε
    rw [hm0]
    norm_num
