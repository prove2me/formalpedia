-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.erdos_partition_limit_constant
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:40:50.799311+00:00
-- url     : https://prove2.me/submissions/6a1ca864-59fe-43a4-ab78-16937a8c3138

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance_x1
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankDropKer
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Pker_rankDrop_tail_majorant
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_hit
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_same_ceiling_enterBand_overlap
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_erdos_limit_constant_of_renewal
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

lemma partsLE_eq_weightFiberCard (K n : ℕ) :
    partsLE K n = weightFiberCard K n := by
  change Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} =
    @Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n}
      (weightFiberFintype K n)
  exact @Fintype.card_congr
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}
    {q : Fin K → ℕ // multiplicityWeight K q = n}
    inferInstance
    (weightFiberFintype K n)
    (boundedPartitionEquivCounts K n)

lemma partsLE_eq_part_of_le {K n : ℕ} (h : n ≤ K) :
    (partsLE K n : ℝ) = part n := by
  dsimp [partsLE, part]
  exact_mod_cast Fintype.card_congr (boundedPartitionTopEquiv K n h)

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

theorem part_zero : part 0 = 1 := by
  simp [part]

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

lemma part_eq_weightFiberCard_of_le {K n : ℕ} (h : n ≤ K) :
    part n = (weightFiberCard K n : ℝ) := by
  rw [← partsLE_eq_part_of_le (K := K) (n := n) h]
  exact_mod_cast (partsLE_eq_weightFiberCard K n)

lemma weight_update_add {K : ℕ} (i : Fin K) (k : ℕ) (q : Fin K → ℕ) :
    multiplicityWeight K (Function.update q i (q i + k)) =
      multiplicityWeight K q + (i.1 + 1) * k := by
  classical
  unfold multiplicityWeight
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * Function.update q i (q i + k) j) hi]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q j) hi]
  have htail :
      (∑ x ∈ Finset.univ.erase i,
          (x.1 + 1) * Function.update q i (q i + k) x) =
        ∑ x ∈ Finset.univ.erase i, (x.1 + 1) * q x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [hxi]
  rw [htail]
  rw [Function.update_self, Nat.mul_add]
  omega

lemma weight_update_sub {K : ℕ} (i : Fin K) {k : ℕ} (q : Fin K → ℕ) (hk : k ≤ q i) :
    multiplicityWeight K (Function.update q i (q i - k)) + (i.1 + 1) * k =
      multiplicityWeight K q := by
  classical
  unfold multiplicityWeight
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * Function.update q i (q i - k) j) hi]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q j) hi]
  have htail :
      (∑ x ∈ Finset.univ.erase i,
          (x.1 + 1) * Function.update q i (q i - k) x) =
        ∑ x ∈ Finset.univ.erase i, (x.1 + 1) * q x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [hxi]
  rw [htail]
  rw [Function.update_self]
  have hmain :
      (i.1 + 1) * (q i - k) + (i.1 + 1) * k = (i.1 + 1) * q i := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  omega

noncomputable def addCoordinateFiberEquiv {K t : ℕ} (i : Fin K) (k : ℕ)
    (hkv : (i.1 + 1) * k ≤ t) :
    {q : Fin K → ℕ // multiplicityWeight K q = t - (i.1 + 1) * k} ≃
      {q : {q : Fin K → ℕ // multiplicityWeight K q = t} // k ≤ q.1 i} where
  toFun q := by
    refine ⟨⟨Function.update q.1 i (q.1 i + k), ?_⟩, ?_⟩
    · rw [weight_update_add, q.2]
      omega
    · simp
  invFun q := by
    refine ⟨Function.update q.1.1 i (q.1.1 i - k), ?_⟩
    have hsub := weight_update_sub i q.1.1 q.2
    rw [q.1.2] at hsub
    omega
  left_inv := by
    intro q
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hji]
  right_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst hji
      simp [Nat.sub_add_cancel q.2]
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hji]

lemma fiber_coord_le_div {K t : ℕ} (i : Fin K)
    (q : {q : Fin K → ℕ // multiplicityWeight K q = t}) :
    q.1 i ≤ t / (i.1 + 1) := by
  have hterm : (i.1 + 1) * q.1 i ≤ multiplicityWeight K q.1 := by
    unfold multiplicityWeight
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q.1 j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [q.2] at hterm
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos i.1)).2 (by
    simpa [Nat.mul_comm] using hterm)

lemma sum_nat_eq_sum_card_ge {α : Type*} [Fintype α] (f : α → ℕ) (B : ℕ)
    (hB : ∀ a, f a ≤ B) :
    (∑ a : α, f a) =
      ∑ k ∈ Finset.Icc 1 B, Fintype.card {a : α // k ≤ f a} := by
  classical
  calc
    (∑ a : α, f a)
        = ∑ a : α, ∑ k ∈ Finset.Icc 1 B, if k ≤ f a then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          have hfilter :
              (Finset.Icc 1 B).filter (fun k => k ≤ f a) = Finset.Icc 1 (f a) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc]
            have hBa := hB a
            omega
          have hsum :
              (∑ k ∈ Finset.Icc 1 B, if k ≤ f a then 1 else 0)
                = ((Finset.Icc 1 B).filter (fun k => k ≤ f a)).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [hsum, hfilter]
          simp
    _ = ∑ k ∈ Finset.Icc 1 B, ∑ a : α, if k ≤ f a then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 B, Fintype.card {a : α // k ≤ f a} := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [Fintype.card_subtype]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma fiber_coord_sum_eq (K t : ℕ) (i : Fin K) :
    letI := weightFiberFintype K t
    (∑ q : {q : Fin K → ℕ // multiplicityWeight K q = t}, q.1 i) =
      ∑ k ∈ Finset.Icc 1 (t / (i.1 + 1)),
        weightFiberCard K (t - (i.1 + 1) * k) := by
  classical
  letI := weightFiberFintype K t
  rw [sum_nat_eq_sum_card_ge
    (f := fun q : {q : Fin K → ℕ // multiplicityWeight K q = t} => q.1 i)
    (B := t / (i.1 + 1)) (fun q => fiber_coord_le_div i q)]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ t / (i.1 + 1) := (Finset.mem_Icc.mp hk).2
  have hkv : (i.1 + 1) * k ≤ t := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (Nat.succ_pos i.1)).1 hk_le
  letI := weightFiberFintype K (t - (i.1 + 1) * k)
  change
      Fintype.card {q : {q : Fin K → ℕ // multiplicityWeight K q = t} // k ≤ q.1 i} =
        Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = t - (i.1 + 1) * k}
  exact (Fintype.card_congr (addCoordinateFiberEquiv i k hkv)).symm

lemma weightFiber_double_recurrence (n : ℕ) :
    n * weightFiberCard n n =
      ∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k) := by
  classical
  letI := weightFiberFintype n n
  calc
    n * weightFiberCard n n
        = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, n := by
          simp [weightFiberCard, Finset.sum_const, mul_comm]
    _ = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, multiplicityWeight n q.1 := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          exact q.2.symm
    _ = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n},
          ∑ i : Fin n, (i.1 + 1) * q.1 i := by
          rfl
    _ = ∑ i : Fin n,
          ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, (i.1 + 1) * q.1 i := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, (i.1 + 1) *
          ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, q.1 i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [fiber_coord_sum_eq n n i]

lemma divisor_reindex_sum (n : ℕ) (F : ℕ → ℕ) :
    (∑ v ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 (n / v), v * F (v * k)) =
      ∑ m ∈ Finset.Icc 1 n, (∑ d ∈ m.divisors, d) * F m := by
  classical
  let left : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun v => Finset.Icc 1 (n / v))
  let right : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun m => m.divisors)
  have hbij :
      (∑ x ∈ left, x.1 * F (x.1 * x.2)) =
        ∑ y ∈ right, y.2 * F y.1 := by
    refine Finset.sum_bij
      (fun x _hx => (⟨x.1 * x.2, x.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      dsimp [left, right] at hx ⊢
      rw [Finset.mem_sigma] at hx ⊢
      rcases hx with ⟨hv, hk⟩
      rw [Finset.mem_Icc] at hv hk ⊢
      constructor
      · constructor
        · exact Nat.mul_pos hv.1 hk.1
        · have hmul := (Nat.le_div_iff_mul_le hv.1).1 hk.2
          simpa [Nat.mul_comm] using hmul
      · exact Nat.mem_divisors.mpr
          ⟨Nat.dvd_mul_right x.1 x.2,
            Nat.mul_ne_zero (Nat.ne_of_gt hv.1) (Nat.ne_of_gt hk.1)⟩
    · intro x hx y hy hxy
      dsimp [left] at hx hy
      rw [Finset.mem_sigma] at hx hy
      rcases hx with ⟨hvx, hkx⟩
      rcases hy with ⟨hvy, hky⟩
      rw [Finset.mem_Icc] at hvx hkx hvy hky
      cases x with
      | mk vx kx =>
      cases y with
      | mk vy ky =>
      simp at hxy
      rcases hxy with ⟨hmul, hv⟩
      subst hv
      have hk : kx = ky := Nat.eq_of_mul_eq_mul_left hvx.1 hmul
      subst hk
      rfl
    · intro y hy
      dsimp [right] at hy
      rw [Finset.mem_sigma] at hy
      rcases hy with ⟨hm, hd⟩
      rw [Finset.mem_Icc] at hm
      have hdvd : y.2 ∣ y.1 := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < y.2 := Nat.pos_of_mem_divisors hd
      have hyle : y.2 ≤ y.1 := Nat.le_of_dvd hm.1 hdvd
      refine ⟨(⟨y.2, y.1 / y.2⟩ : Sigma fun _ : ℕ => ℕ), ?_, ?_⟩
      · dsimp [left]
        rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_Icc]
          exact ⟨hdpos, hyle.trans hm.2⟩
        · rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hyle hdpos
          · exact Nat.div_le_div_right hm.2
      · ext <;> simp [Nat.mul_div_cancel' hdvd]
    · intro x hx
      rfl
  calc
    (∑ v ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 (n / v), v * F (v * k))
        = ∑ x ∈ left, x.1 * F (x.1 * x.2) := by
          dsimp [left]
          rw [Finset.sum_sigma']
    _ = ∑ y ∈ right, y.2 * F y.1 := hbij
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors, d * F m := by
          dsimp [right]
          rw [Finset.sum_sigma']
    _ = ∑ m ∈ Finset.Icc 1 n, (∑ d ∈ m.divisors, d) * F m := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [Finset.sum_mul]

lemma weightFiber_divisor_recurrence (n : ℕ) :
    n * weightFiberCard n n =
      ∑ m ∈ Finset.Icc 1 n,
        (∑ d ∈ m.divisors, d) * weightFiberCard n (n - m) := by
  rw [weightFiber_double_recurrence]
  calc
    (∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k))
        = ∑ v ∈ Finset.Icc 1 n, v *
            ∑ k ∈ Finset.Icc 1 (n / v), weightFiberCard n (n - v * k) := by
          exact sum_fin_succ_eq_Icc n
            (fun v => v * ∑ k ∈ Finset.Icc 1 (n / v), weightFiberCard n (n - v * k))
    _ = ∑ v ∈ Finset.Icc 1 n,
          ∑ k ∈ Finset.Icc 1 (n / v), v * weightFiberCard n (n - v * k) := by
          refine Finset.sum_congr rfl ?_
          intro v _hv
          rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, d) * weightFiberCard n (n - m) := by
          exact divisor_reindex_sum n (fun m => weightFiberCard n (n - m))

theorem partition_sigma_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * part n =
      ∑ m ∈ Finset.Icc 1 n, sigmaR m * part (n - m) := by
  have hnat := weightFiber_divisor_recurrence n
  have hrealCast :
      ((n * weightFiberCard n n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := by
    simpa using congrArg (fun a : ℕ => (a : ℝ)) hnat
  have hreal :
      (n : ℝ) * (weightFiberCard n n : ℝ) =
        ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := by
    simpa [Nat.cast_mul] using hrealCast
  calc
    (n : ℝ) * part n
        = (n : ℝ) * (weightFiberCard n n : ℝ) := by
          rw [part_eq_weightFiberCard_of_le (K := n) (n := n) (by
            have _ : 1 ≤ n := hn
            exact le_rfl)]
    _ = ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := hreal
    _ = ∑ m ∈ Finset.Icc 1 n, sigmaR m * part (n - m) := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [sigmaR_eq_sum_divisors]
          rw [part_eq_weightFiberCard_of_le (K := n) (n := n - m) (Nat.sub_le n m)]

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma sigmaR_le_square {n : ℕ} (hn : 1 ≤ n) :
    Sigma.sigmaR n ≤ (n : ℝ) ^ 2 := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  have hcard_nat : n.divisors.card ≤ n := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by
        simp
  have hsum_le :
      (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
  calc
    (∑ d ∈ n.divisors, (d : ℝ))
        ≤ ∑ _d ∈ n.divisors, (n : ℝ) := hsum_le
    _ = (n.divisors.card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (n : ℝ) ^ 2 := by
          have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_nat
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          nlinarith

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

theorem u_recurrence (n : ℕ) (hn : 2 ≤ n) :
    u n =
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
        boundaryTerm n := by
  classical
  have hn1 : 1 ≤ n := hn.trans' (by norm_num)
  have hrec := Sigma.partition_sigma_recurrence n hn1
  have hsplit :
      (∑ m ∈ Finset.Icc 1 n, Sigma.sigmaR m * Partitions.part (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0 := by
    have htop :
        (∑ m ∈ Finset.Icc 1 ((n - 1) + 1),
            Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) =
          (∑ m ∈ Finset.Icc 1 (n - 1),
              Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) +
            Sigma.sigmaR ((n - 1) + 1) *
              Partitions.part (((n - 1) + 1) - ((n - 1) + 1)) := by
      exact Finset.sum_Icc_succ_top
        (a := 1) (b := n - 1)
        (by omega)
        (fun m => Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m))
    have hnsub : (n - 1) + 1 = n := by omega
    simpa [hnsub] using htop
  have hmain :
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    have hmle : m ≤ n - 1 := hmI.2
    have hmn_pos_nat : 0 < n - m := by omega
    have hmn_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hmn_pos_nat
    have hmn_ne : ((n - m : ℕ) : ℝ) ≠ 0 := hmn_pos.ne'
    have hsqrt_add :
        -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) +
            (-C * Real.sqrt ((n - m : ℕ) : ℝ)) =
          -C * Real.sqrt (n : ℝ) := by
      ring
    calc
      erdosWeight n m * u (n - m)
          =
            (Sigma.sigmaR m / ((n - m : ℕ) : ℝ) *
                Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))) *
              (((n - m : ℕ) : ℝ) * Partitions.part (n - m) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  rfl
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              (Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  field_simp [hmn_ne]
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ)) := by
                  rw [← Real.exp_add, hsqrt_add]
  calc
    u n
        = ((n : ℝ) * Partitions.part n) *
            Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [u]
    _ = (∑ m ∈ Finset.Icc 1 n,
            Sigma.sigmaR m * Partitions.part (n - m)) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hrec]
    _ = ((∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hsplit]
    _ = (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) +
          Sigma.sigmaR n * Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [Partitions.part_zero]
          rw [add_mul, Finset.sum_mul]
          ring
    _ = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
          boundaryTerm n := by
          rw [hmain]
          rfl

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Barrier-package foundations (HR Stage I.5)

Definitions and the easy layers of the logarithmic-barrier route to two-sided boundedness
of `u` (route R6, audited): `kernelMass`/`kernelWindow`, the barriers `1 ∓ A/log(n+E)`,
the slack scale `1/(√n log²(n+E))`, the positive fixed window (from the banked
`erdos_kernel_window` + integral positivity), barrier range bounds, and boundary-vs-slack
negligibility (from the banked cube-decay lemma).  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Upper barrier `1 − A/log(n+E)`. -/
noncomputable def upperBarrier (A E : ℝ) (n : ℕ) : ℝ :=
  1 - A / Real.log ((n : ℝ) + E)

/-- The barrier slack scale `1/(√n·log²(n+E))`. -/
noncomputable def barrierSlack (E : ℝ) (n : ℕ) : ℝ :=
  1 / (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2)

/-- **Positive fixed window**: some window `(a₀√n, b₀√n]` carries kernel mass `≥ μ > 0`
eventually. -/
theorem erdos_kernel_fixed_window_pos :
    ∃ a₀ b₀ μ : ℝ, 0 < a₀ ∧ a₀ < b₀ ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop, μ ≤ kernelWindow a₀ b₀ n := by
  have hC := C_pos
  -- the limit value: I := ∫_1^2 (π²/6) y e^{−(C/2)y} dy > 0
  have hIpos : 0 < Model.modelIntegral C 1 2 := by
    rw [Model.modelIntegral]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · -- integrability
      have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
        have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
          continuous_const.mul continuous_id
        have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact h1.mul h2
      exact hc.intervalIntegrable _ _
    · intro y hy
      have hy1 : (1 : ℝ) < y := hy.1
      have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
      have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
      nlinarith [mul_pos (mul_pos hπ (by linarith : (0:ℝ) < y)) he]
    · norm_num
  refine ⟨1, 2, Model.modelIntegral C 1 2 / 2, one_pos, one_lt_two, by positivity, ?_⟩
  -- the window mass tends to the integral, so eventually exceeds half of it
  have hwin := Model.erdos_kernel_window (a := 1) (b := 2) zero_le_one one_lt_two
  have hev := (tendsto_order.1 hwin).1 (Model.modelIntegral C 1 2 / 2) (by linarith)
  filter_upwards [hev] with n hn
  exact hn.le

/-- Upper barrier eventually in `(0, 1]`. -/
lemma upperBarrier_eventually_pos_bdd {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 0 < upperBarrier A E n ∧ upperBarrier A E n ≤ 1 := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + E)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  have hev := hlog.eventually_gt_atTop A
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have : (1 : ℝ) < (n : ℝ) + E := by linarith
    exact Real.log_pos this
  constructor
  · have : A / Real.log ((n : ℝ) + E) < 1 := by
      rw [div_lt_one hlogpos]
      exact hn
    rw [upperBarrier]
    linarith
  · rw [upperBarrier]
    have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
    linarith

/-- Barrier slack is eventually positive. -/
lemma barrierSlack_eventually_pos {E : ℝ} (hE : 3 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 0 < barrierSlack E n := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hgt : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [barrierSlack]
  positivity

/-- `n⁵·e^{−C√n} → 0`. -/
private lemma nat_pow5_mul_exp_neg_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)) ^ 5 * Real.exp (-C * Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
  have hC := C_pos
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp
    (Tendsto.const_mul_atTop hC
      (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))
  have hbase' : Tendsto
      (fun n : ℕ => (C * Real.sqrt (n : ℝ)) ^ 10 * Real.exp (-(C * Real.sqrt (n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp] using hbase
  have hconst := hbase'.const_mul (1 / C ^ 10)
  rw [mul_zero] at hconst
  refine hconst.congr fun n => ?_
  have hsq : Real.sqrt (n : ℝ) ^ 10 = ((n : ℝ)) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul]
    congr 1
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have harg : -(C * Real.sqrt (n : ℝ)) = -C * Real.sqrt (n : ℝ) := by ring
  rw [mul_pow, hsq, harg]
  field_simp

/-- **Boundary is negligible against the slack**: `boundaryTerm n ≤ δ·barrierSlack E n`
eventually, for every `δ > 0`. -/
lemma boundaryTerm_le_barrierSlack {E δ : ℝ} (hE : 3 ≤ E) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, boundaryTerm n ≤ δ * barrierSlack E n := by
  have hC := C_pos
  have hev := (tendsto_order.1 nat_pow5_mul_exp_neg_sqrt_tendsto_zero).2
    (δ / 4) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1, eventually_ge_atTop ⌈E⌉₊]
    with n hn5 hn1 hnE
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hEn : E ≤ (n : ℝ) := le_trans (Nat.le_ceil E) (by exact_mod_cast hnE)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hgt1 : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt1
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hEpos : 0 < Real.exp (-C * Real.sqrt (n : ℝ)) := Real.exp_pos _
  -- boundary ≤ n²·e^{−C√n}
  have hbd : boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := by
    rw [boundaryTerm]
    exact mul_le_mul_of_nonneg_right (sigmaR_le_square hn1) hEpos.le
  -- √n·log²(n+E) ≤ 4n³
  have hlog_le : Real.log ((n : ℝ) + E) ≤ 2 * (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + E)
    linarith
  have hs_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (n : ℝ) := Real.sqrt_sq hnpos.le
  have hfac : Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2 ≤ 4 * (n : ℝ) ^ 3 := by
    have hlogsq : (Real.log ((n : ℝ) + E)) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      nlinarith [hlogpos.le, hlog_le]
    calc Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2
        ≤ (n : ℝ) * (4 * (n : ℝ) ^ 2) :=
          mul_le_mul hs_le hlogsq (by positivity) hnpos.le
      _ = 4 * (n : ℝ) ^ 3 := by ring
  -- assemble: boundary·(√n·log²) ≤ 4n⁵e^{−C√n} ≤ δ
  have hd_pos : 0 < Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2 := by positivity
  rw [barrierSlack, mul_one_div, le_div_iff₀ hd_pos]
  calc boundaryTerm n * (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2)
      ≤ ((n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ))) *
          (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2) :=
        mul_le_mul_of_nonneg_right hbd hd_pos.le
    _ ≤ ((n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ))) * (4 * (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = 4 * ((n : ℝ) ^ 5 * Real.exp (-C * Real.sqrt (n : ℝ))) := by ring
    _ ≤ 4 * (δ / 4) := by linarith [hn5]
    _ = δ := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Barrier gap on a positive kernel window (R6 lemma 4)

On the window `a₀√n < m ≤ b₀√n` the logarithmic barrier moves by at least a fixed
multiple of the slack: both

  `upperBarrier n − upperBarrier (n−m)` and `lowerBarrier (n−m) − lowerBarrier n`

equal `A/log(n−m+E) − A/log(n+E)`, and

  `log(n+E) − log(n−m+E) ≥ m/(n+E) ≥ (a₀/2)·(1/√n)`

(by `log r ≤ r − 1` on `r = (n−m+E)/(n+E)`), while the denominator product is at most
`log²(n+E)`.  Hence the gap is `≥ (A·a₀/2)·barrierSlack E n` eventually.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Core gap estimate: on the window, `A/log(n−m+E) − A/log(n+E) ≥ (A a₀/2)·slack`. -/
lemma barrier_core_gap_on_window
    {A E a₀ b₀ : ℝ} (hA : 0 < A) (hE : 3 ≤ E)
    (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      a₀ * Real.sqrt (n : ℝ) < (m : ℝ) →
      (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ) →
      A / Real.log (((n - m : ℕ) : ℝ) + E) - A / Real.log ((n : ℝ) + E)
        ≥ (A * a₀ / 2) * barrierSlack E n := by
  have hb₀ : 0 < b₀ := lt_trans ha₀ hab₀
  -- eventual regime: n ≥ 1, n ≥ E, 2b₀ ≤ √n
  have hev : ∀ᶠ n : ℕ in atTop,
      (1 ≤ n ∧ E ≤ (n : ℝ)) ∧ 2 * b₀ ≤ Real.sqrt (n : ℝ) := by
    have h1 := eventually_ge_atTop 1
    have h2 : ∀ᶠ n : ℕ in atTop, E ≤ (n : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈E⌉₊] with n hn
      exact le_trans (Nat.le_ceil E) (by exact_mod_cast hn)
    have h3 : ∀ᶠ n : ℕ in atTop, 2 * b₀ ≤ Real.sqrt (n : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈(2 * b₀) ^ 2⌉₊] with n hn
      have hcast : ((2 * b₀) ^ 2 : ℝ) ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
      have h2b : (0 : ℝ) ≤ 2 * b₀ := by positivity
      calc 2 * b₀ = Real.sqrt ((2 * b₀) ^ 2) := (Real.sqrt_sq h2b).symm
        _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hcast
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    exact ⟨⟨hn1, hn2⟩, hn3⟩
  filter_upwards [hev] with n ⟨⟨hn1, hnE⟩, hsb⟩
  intro m hma hmb
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  -- m ≤ n/2 (window inside the left half)
  have hm_half : 2 * (m : ℝ) ≤ (n : ℝ) := by
    calc 2 * (m : ℝ) ≤ 2 * (b₀ * Real.sqrt (n : ℝ)) := by linarith
      _ = (2 * b₀) * Real.sqrt (n : ℝ) := by ring
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right hsb hspos.le
      _ = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hm_le_n : m ≤ n := by
    have : (m : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hcast_sub : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm_le_n]
    ring
  -- positivity of the logs
  have hgt1 : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogn : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt1
  have hsubgt1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) + E := by
    rw [hcast_sub]
    have : (n : ℝ) - (m : ℝ) ≥ (n : ℝ) / 2 := by linarith
    linarith
  have hlogsub : 0 < Real.log (((n - m : ℕ) : ℝ) + E) := Real.log_pos hsubgt1
  have hlog_mono : Real.log (((n - m : ℕ) : ℝ) + E) ≤ Real.log ((n : ℝ) + E) := by
    apply Real.log_le_log (by linarith)
    rw [hcast_sub]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- numerator bound: log(n+E) − log(n−m+E) ≥ m/(n+E)
  have hnum : Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)
      ≥ (m : ℝ) / ((n : ℝ) + E) := by
    -- log r ≤ r − 1 with r = (n−m+E)/(n+E)
    have hr_pos : 0 < (((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E) := by
      apply div_pos (by linarith) (by linarith)
    have hlogr := Real.log_le_sub_one_of_pos hr_pos
    have hlog_div : Real.log ((((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E))
        = Real.log (((n - m : ℕ) : ℝ) + E) - Real.log ((n : ℝ) + E) :=
      Real.log_div (by linarith) (by linarith)
    rw [hlog_div] at hlogr
    have hfrac : (((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E) - 1
        = -((m : ℝ) / ((n : ℝ) + E)) := by
      rw [hcast_sub]
      field_simp
      ring
    rw [hfrac] at hlogr
    linarith
  -- (a₀/2)·(1/√n) ≤ m/(n+E)
  have hm_lower : (a₀ / 2) * (1 / Real.sqrt (n : ℝ)) ≤ (m : ℝ) / ((n : ℝ) + E) := by
    have hden : (n : ℝ) + E ≤ 2 * (n : ℝ) := by linarith
    have hge : (a₀ * Real.sqrt (n : ℝ)) / (2 * (n : ℝ)) ≤ (m : ℝ) / ((n : ℝ) + E) :=
      div_le_div₀ (Nat.cast_nonneg m) hma.le (by linarith) hden
    have heq : (a₀ * Real.sqrt (n : ℝ)) / (2 * (n : ℝ))
        = (a₀ / 2) * (1 / Real.sqrt (n : ℝ)) := by
      have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      field_simp
      nlinarith [hss]
    rw [← heq]
    exact hge
  -- assemble: gap = A·(log(n+E) − log(n−m+E))/(log(n−m+E)·log(n+E)) ≥ ...
  have hgap_eq : A / Real.log (((n - m : ℕ) : ℝ) + E) - A / Real.log ((n : ℝ) + E)
      = A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)) := by
    field_simp
  rw [hgap_eq, ge_iff_le, barrierSlack]
  -- target: (A a₀/2)·(1/(√n log²(n+E))) ≤ A·num/(logsub·logn)
  have hden_le : Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)
      ≤ (Real.log ((n : ℝ) + E)) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlog_mono hlogn.le
    nlinarith [this]
  have hnum_ge : (a₀ / 2) * (1 / Real.sqrt (n : ℝ))
      ≤ Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E) :=
    le_trans hm_lower hnum
  calc (A * a₀ / 2) * (1 / (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2))
      = A * ((a₀ / 2) * (1 / Real.sqrt (n : ℝ))) / (Real.log ((n : ℝ) + E)) ^ 2 := by
        field_simp
    _ ≤ A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log ((n : ℝ) + E)) ^ 2 := by
        gcongr
    _ ≤ A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)) := by
        have hnumpos : 0 ≤ A * (Real.log ((n : ℝ) + E) -
            Real.log (((n - m : ℕ) : ℝ) + E)) := by
          have : 0 ≤ Real.log ((n : ℝ) + E) -
              Real.log (((n - m : ℕ) : ℝ) + E) := by linarith [hlog_mono]
          positivity
        gcongr

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Super/subharmonicity of the logarithmic barriers (R6 lemmas 5–6, conditional on rate)

Given the (yet-unbanked) critical mass rate in `o(slack)` form — for every `ρ > 0`,
eventually `|kernelMass n − 1| ≤ ρ·barrierSlack E n` — the kernel averages the barriers
strictly inward:

  `Σ W(n,m)·H₊(n−m) ≤ H₊(n) − δ·slack`   and   `Σ W(n,m)·H₋(n−m) ≥ H₋(n) + δ·slack`.

Split at the positive fixed window: off-window terms move the right way by barrier
monotonicity; window terms gain `c·slack` each (BarrierGap core, `c = a₀/2` at `A = 1`);
the mass error is absorbed by instantiating `ρ` small against `c·μ`.  The rate hypothesis is
the one remaining analytic brick (second-order cancellation — see HANDOFF design notes).
Opus-authored; CONDITIONAL on the rate hypothesis (no axioms — hypothesis-parameterized).
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `upperBarrier` is monotone in `n` (for `A > 0`, `E ≥ 3`). -/
lemma upperBarrier_mono {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    Monotone (upperBarrier A E) := by
  intro k l hkl
  have hk : (1 : ℝ) < (k : ℝ) + E := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hl : (1 : ℝ) < (l : ℝ) + E := by
    have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have hlogk : 0 < Real.log ((k : ℝ) + E) := Real.log_pos hk
  have hlogl : 0 < Real.log ((l : ℝ) + E) := Real.log_pos hl
  have hmono : Real.log ((k : ℝ) + E) ≤ Real.log ((l : ℝ) + E) := by
    apply Real.log_le_log (by linarith)
    have : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  rw [upperBarrier, upperBarrier]
  have : A / Real.log ((l : ℝ) + E) ≤ A / Real.log ((k : ℝ) + E) :=
    div_le_div_of_nonneg_left hA.le hlogk hmono
  linarith

/-- `upperBarrier ≤ 1` always (for `A > 0`, `E ≥ 3`). -/
lemma upperBarrier_le_one {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (n : ℕ) :
    upperBarrier A E n ≤ 1 := by
  have h1 : (1 : ℝ) < (n : ℝ) + E := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
  rw [upperBarrier]
  have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
  linarith

/-- The exact window/complement split of a kernel-weighted sum. -/
private lemma kernel_sum_split (a b : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * g (n - m))
      = (∑ m ∈ Finset.Icc 1 (n - 1),
          if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
          then erdosWeight n m * g (n - m) else 0)
        + (∑ m ∈ Finset.Icc 1 (n - 1),
          if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
          then 0 else erdosWeight n m * g (n - m)) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
  · rw [if_pos hwin, if_pos hwin, add_zero]
  · rw [if_neg hwin, if_neg hwin, zero_add]

/--
**Upper barrier is superharmonic, conditional on the mass rate** (R6 lemma 5):
if `|kernelMass n − 1| ≤ ρ·barrierSlack E n` eventually, then for a suitable `A` the kernel
average of `upperBarrier A E` sits below `upperBarrier A E n − δ·slack`.
-/
lemma upperBarrier_one_pos {E : ℝ} (hE : 3 ≤ E) (k : ℕ) : 0 < upperBarrier 1 E k := by
  have hkE : (0:ℝ) < (k:ℝ) + E := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlog : 1 < Real.log ((k:ℝ) + E) := by
    rw [Real.lt_log_iff_exp_lt hkE]
    have := Real.exp_one_lt_three
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [upperBarrier]
  have hdiv : 1 / Real.log ((k:ℝ) + E) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

theorem upperBarrier_kernel_superharmonic_of_rate
    {E : ℝ} (hE : 3 ≤ E)
    (hrate : ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ n : ℕ in atTop, |kernelMass n - 1| ≤ ρ * barrierSlack E n) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ (∀ k : ℕ, 0 < upperBarrier A E k) ∧
      ∀ᶠ n : ℕ in atTop,
        (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
          ≤ upperBarrier A E n - δ * barrierSlack E n := by
  classical
  obtain ⟨a₀, b₀, μ, ha₀, hab₀, hμ, hwinmass⟩ := erdos_kernel_fixed_window_pos
  have hA : (0 : ℝ) < 1 := one_pos
  set A : ℝ := 1 with hAdef
  set c : ℝ := A * a₀ / 2 with hcdef
  have hc : 0 < c := by rw [hcdef, hAdef]; positivity
  set ρ : ℝ := c * μ / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  refine ⟨A, c * μ - ρ, hA, by rw [hρdef]; nlinarith [mul_pos hc hμ],
    (fun k => by rw [hAdef]; exact upperBarrier_one_pos hE k), ?_⟩
  filter_upwards [barrier_core_gap_on_window hA hE ha₀ hab₀, hwinmass, hrate ρ hρ,
    barrierSlack_eventually_pos hE, upperBarrier_eventually_pos_bdd hA hE,
    eventually_ge_atTop 1] with n hgap hwin hr hsl hbdd hn1
  -- per-term bounds on the two pieces
  have hsplit := kernel_sum_split a₀ b₀ n (upperBarrier A E)
  have hwin_term : (∑ m ∈ Finset.Icc 1 (n - 1),
      if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      then erdosWeight n m * upperBarrier A E (n - m) else 0)
      ≤ (upperBarrier A E n - c * barrierSlack E n) * kernelWindow a₀ b₀ n := by
    rw [kernelWindow, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
    · rw [if_pos hwinm, if_pos hwinm]
      have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
      have hcore := hgap m hwinm.1 hwinm.2
      -- upperBarrier(n−m) ≤ upperBarrier n − c·slack
      have hble : upperBarrier A E (n - m) ≤ upperBarrier A E n - c * barrierSlack E n := by
        rw [upperBarrier, upperBarrier] at *
        rw [hcdef]
        linarith [hcore]
      calc erdosWeight n m * upperBarrier A E (n - m)
          ≤ erdosWeight n m * (upperBarrier A E n - c * barrierSlack E n) :=
            mul_le_mul_of_nonneg_left hble hW
        _ = (upperBarrier A E n - c * barrierSlack E n) * erdosWeight n m := by ring
    · rw [if_neg hwinm, if_neg hwinm, mul_zero]
  have hoff_term : (∑ m ∈ Finset.Icc 1 (n - 1),
      if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      then 0 else erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n) := by
    have hKW : kernelMass n - kernelWindow a₀ b₀ n
        = ∑ m ∈ Finset.Icc 1 (n - 1),
            (if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
             then 0 else erdosWeight n m) := by
      rw [kernelMass, kernelWindow, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro m _hm
      by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      · rw [if_pos hwinm, if_pos hwinm, sub_self]
      · rw [if_neg hwinm, if_neg hwinm, sub_zero]
    rw [hKW, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
    · rw [if_pos hwinm, if_pos hwinm, mul_zero]
    · rw [if_neg hwinm, if_neg hwinm]
      have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
      have hmle : n - m ≤ n := Nat.sub_le n m
      have hmono := upperBarrier_mono hA hE hmle
      calc erdosWeight n m * upperBarrier A E (n - m)
          ≤ erdosWeight n m * upperBarrier A E n :=
            mul_le_mul_of_nonneg_left hmono hW
        _ = upperBarrier A E n * erdosWeight n m := by ring
  -- assemble
  have htotal : (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * kernelMass n - c * barrierSlack E n * kernelWindow a₀ b₀ n := by
    rw [hsplit]
    have := add_le_add hwin_term hoff_term
    calc (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then erdosWeight n m * upperBarrier A E (n - m) else 0)
        + (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then 0 else erdosWeight n m * upperBarrier A E (n - m))
        ≤ (upperBarrier A E n - c * barrierSlack E n) * kernelWindow a₀ b₀ n
          + upperBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n) := this
      _ = upperBarrier A E n * kernelMass n
          - c * barrierSlack E n * kernelWindow a₀ b₀ n := by ring
  -- mass error absorption: H·mass ≤ H + |mass−1| (|H| ≤ 1 here), window ≥ μ
  have hH1 : |upperBarrier A E n| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hbdd.1]
    · exact hbdd.2
  have hmass_abs : upperBarrier A E n * kernelMass n
      ≤ upperBarrier A E n + ρ * barrierSlack E n := by
    have h1 : upperBarrier A E n * kernelMass n
        = upperBarrier A E n + upperBarrier A E n * (kernelMass n - 1) := by ring
    rw [h1]
    have h2 : upperBarrier A E n * (kernelMass n - 1)
        ≤ |upperBarrier A E n * (kernelMass n - 1)| := le_abs_self _
    have h3 : |upperBarrier A E n * (kernelMass n - 1)|
        = |upperBarrier A E n| * |kernelMass n - 1| := abs_mul _ _
    have h4 : |upperBarrier A E n| * |kernelMass n - 1| ≤ 1 * (ρ * barrierSlack E n) := by
      apply mul_le_mul hH1 hr (abs_nonneg _) one_pos.le
    linarith
  have hwin_lower : c * barrierSlack E n * kernelWindow a₀ b₀ n
      ≥ c * barrierSlack E n * μ := by
    apply mul_le_mul_of_nonneg_left hwin
    positivity
  calc (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * kernelMass n - c * barrierSlack E n * kernelWindow a₀ b₀ n :=
        htotal
    _ ≤ (upperBarrier A E n + ρ * barrierSlack E n) - c * barrierSlack E n * μ := by
        linarith [hmass_abs, hwin_lower]
    _ = upperBarrier A E n - (c * μ - ρ) * barrierSlack E n := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Boundedness of `u` by barrier induction (R6 lemmas 8–12, conditional)

Strong induction on the Erdős recurrence against super/subharmonic barriers:

* `u_upper_of_superharmonic` — if the upper barrier is superharmonic (with positive values)
  then `u n ≤ M·H₊(n)` for all `n`, hence `u` is eventually bounded above;
* `u_lower_of_subharmonic` — if the lower barrier is subharmonic then `c·H₋(n) ≤ u n` for
  all `n ≥ 1`, hence `liminf u > 0`.

Both take the harmonic inequality as a hypothesis (supplied conditionally-on-rate by
`BarrierHarmonic`; unconditionally once the mass-rate brick lands).  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Upper boundedness by barrier induction** (R6 lemma 8): a globally positive superharmonic
upper barrier dominates `u` up to a constant.
-/
theorem u_upper_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, u n ≤ M * upperBarrier A E n := by
  classical
  -- threshold where superharmonicity + boundary control + n ≥ 2 all hold
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsuper
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (boundaryTerm_le_barrierSlack hE hδ)
  set N₀ : ℕ := max (max N₁ N₂) 2 with hN₀def
  -- M covers the initial segment and is ≥ 1
  have hne_range : (Finset.range (N₀ + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  set M₀ : ℝ := (Finset.range (N₀ + 1)).sup' hne_range
    (fun k => u k / upperBarrier A E k) with hM₀def
  set M : ℝ := max M₀ 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨M, hMpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ N₀
    · -- initial segment: M ≥ u n / H₊ n
      have hmem : n ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
      have hsup : u n / upperBarrier A E n ≤ M₀ :=
        Finset.le_sup' (fun k => u k / upperBarrier A E k) hmem
      have hHpos := hpos n
      have : u n / upperBarrier A E n ≤ M := le_trans hsup (le_max_left _ _)
      calc u n = (u n / upperBarrier A E n) * upperBarrier A E n := by
            field_simp
        _ ≤ M * upperBarrier A E n :=
            mul_le_mul_of_nonneg_right this hHpos.le
    · -- inductive step via the recurrence
      push_neg at hsmall
      have hn2 : 2 ≤ n := by omega
      have hnN₁ : N₁ ≤ n := by omega
      have hnN₂ : N₂ ≤ n := by omega
      have hrec := u_recurrence n hn2
      have hsup_n := hN₁ n hnN₁
      have hbdy_n := hN₂ n hnN₂
      -- termwise IH: u (n−m) ≤ M·H₊(n−m) for m ∈ Icc 1 (n−1)
      have hterm : (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hlt : n - m < n := by omega
        exact mul_le_mul_of_nonneg_left (ih (n - m) hlt) hW
      have hfactor : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (M * upperBarrier A E (n - m)))
          = M * ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        ring
      calc u n = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
            + boundaryTerm n := hrec
        _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)))
            + boundaryTerm n := by linarith [hterm]
        _ = M * (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m))
            + boundaryTerm n := by rw [hfactor]
        _ ≤ M * (upperBarrier A E n - δ * barrierSlack E n)
            + δ * barrierSlack E n := by
            have h1 := mul_le_mul_of_nonneg_left hsup_n hMpos.le
            linarith [h1, hbdy_n]
        _ ≤ M * upperBarrier A E n := by
            have hslack_nonneg : 0 ≤ δ * barrierSlack E n := by
              -- δ > 0 and slack ≥ 0 for n in this regime (n ≥ 2)
              have h1 : (1 : ℝ) < (n : ℝ) + E := by
                have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
                linarith
              have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
              have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
              rw [barrierSlack]
              positivity
            nlinarith [hslack_nonneg, hM1]

/-- Eventual upper bound (R6 lemma 9): `u n ≤ M` eventually. -/
theorem u_limsup_finite_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := u_upper_of_superharmonic hA hE hδ hpos hsuper
  refine ⟨M, hMpos, ?_⟩
  filter_upwards with n
  calc u n ≤ M * upperBarrier A E n := hM n
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (upperBarrier_le_one hA hE n) hMpos.le
    _ = M := mul_one M

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- **Mass rate in `o(slack)` form** (R6 input to the barriers): for every `ρ > 0`, eventually
`|kernelMass n − 1| ≤ ρ·barrierSlack E n`. The `1/n` rate (`kernelMass_sub_one_rate`) beats
`barrierSlack E n = 1/(√n·(log(n+E))²)` because `(log(n+E))² = o(√n)`. -/
theorem kernelMass_rate_vs_slack {E : ℝ} (hE : 3 ≤ E) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMass n - 1| ≤ ρ * barrierSlack E n := by
  obtain ⟨K, hKpos, hK⟩ := kernelMass_sub_one_rate
  intro ρ hρ
  have hElt : (0:ℝ) < E := by linarith
  have hlittleo : (fun x : ℝ => Real.log x ^ (2:ℝ)) =o[Filter.atTop] (fun x => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num)
  have hevR : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ 2 ≤ (ρ / (4 * K)) * x ^ (1/2 : ℝ) := by
    have h := hlittleo.def (show (0:ℝ) < ρ / (4 * K) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have e : Real.log x ^ (2:ℝ) = (Real.log x) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact hx
  have hcomp : Filter.Tendsto (fun n : ℕ => (n:ℝ) + E) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ E tendsto_natCast_atTop_atTop
  filter_upwards [hK, hcomp.eventually hevR, Filter.eventually_ge_atTop (⌈E⌉₊ + 2)]
    with n hk hlogn hnE
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnE_le : (E:ℝ) ≤ (n:ℝ) := by
    have h1 : (⌈E⌉₊ : ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : ⌈E⌉₊ ≤ n)
    exact le_trans (Nat.le_ceil _) h1
  have hL : 0 < Real.log ((n:ℝ) + E) := Real.log_pos (by linarith)
  have hLsq : 0 < (Real.log ((n:ℝ) + E)) ^ 2 := by positivity
  have hsqrtn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  -- (n+E)^{1/2} ≤ 2 √n
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hroot_le : ((n:ℝ) + E) ^ (1/2 : ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt ((n:ℝ) + E) ≤ Real.sqrt (2 * (n:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 2 * Real.sqrt (n:ℝ) := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt (n:ℝ) := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
  -- hence (log(n+E))² ≤ (ρ/(2K)) √n
  have hLbound : (Real.log ((n:ℝ) + E)) ^ 2 ≤ (ρ / (2 * K)) * Real.sqrt (n:ℝ) := by
    calc (Real.log ((n:ℝ) + E)) ^ 2 ≤ (ρ / (4 * K)) * ((n:ℝ) + E) ^ (1/2 : ℝ) := hlogn
      _ ≤ (ρ / (4 * K)) * (2 * Real.sqrt (n:ℝ)) :=
          mul_le_mul_of_nonneg_left hroot_le (by positivity)
      _ = (ρ / (2 * K)) * Real.sqrt (n:ℝ) := by ring
  -- assemble: K/n ≤ ρ·barrierSlack
  have hkey : K / (n:ℝ) ≤ ρ * barrierSlack E n := by
    rw [barrierSlack, mul_one_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
      div_le_iff₀ hnpos]
    -- K * (√n * L²) ≤ ρ * n
    have hstep : K * (Real.sqrt (n:ℝ) * (Real.log ((n:ℝ) + E)) ^ 2)
        ≤ K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLbound hsqrtn.le) hKpos.le
    have heq : K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ))) = (ρ / 2) * (n:ℝ) := by
      rw [show K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ)))
          = (K / (2 * K)) * ρ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) by ring,
        Real.mul_self_sqrt hnpos.le, show K / (2 * K) = 1 / 2 by field_simp]
      ring
    rw [heq] at hstep
    nlinarith [hstep, hρ, hnpos]
  exact le_trans hk hkey

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: §7 unconditional barrier bounds on `u`

The banked kernel-mass rate in `o(slack)` form (`kernelMass_rate_vs_slack`) discharges the
hypotheses of the conditional barrier theorems, giving unconditionally that the normalized
partition function `u` is bounded above (`u_limsup_finite`) and bounded below away from `0`
(`u_liminf_positive`).  Opus-authored.
-/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **`u` is bounded above** (R6): unconditional, via the superharmonic upper barrier fed by the
`o(slack)` mass rate. -/
theorem u_limsup_finite : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨A, δ, hA, hδ, hpos, hsuper⟩ :=
    upperBarrier_kernel_superharmonic_of_rate (le_refl (3:ℝ))
      (kernelMass_rate_vs_slack (le_refl (3:ℝ)))
  exact u_limsup_finite_of_superharmonic hA (le_refl (3:ℝ)) hδ hpos hsuper

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the escape-split overlap contraction

The plain Doeblin inequality `doeblin_average_diff_bound` bounds `|∑p·f − ∑q·f|` by `(1−δ)·W` where `W`
is the oscillation of `f` over the *whole* support.  For the partition predecessor kernel the support is
wide (a single step can drop the rank arbitrarily far), so `W` does not contract.  The fix: split the
support into a high-rank "good" band `G` carrying the overlap `δ` and a low-rank "bad" set carrying only
mass `≤ η`.  Then

  `|∑p·f − ∑q·f| ≤ (1−δ)·W + 3·η·M`,

where `W` is the oscillation of `f` over `G` only and `M` bounds `|f|`.  Driving `η → 0` (escape mass)
and keeping `δ` fixed turns this into the step contraction `V(R) ≤ (1−δ)·V(R−B) + e(R)`, `e → 0`.
Pure nonnegative-sequence algebra — no probability.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Escape-split Doeblin contraction.** Probability vectors `p, q` on `s` with overlap `≥ δ` on the
good band `G`, bad-mass `≤ η`, `f` valued in `[lo, lo+W]` on `G` and `|f| ≤ M`, `|lo| ≤ M`, differ by
at most `(1−δ)·W + 3·η·M`. -/
lemma doeblin_escape_bound {s : Finset ℕ} {p q f : ℕ → ℝ} {δ η lo W M : ℝ}
    (G : ℕ → Prop) [DecidablePred G]
    (hpnn : ∀ k ∈ s, 0 ≤ p k) (hqnn : ∀ k ∈ s, 0 ≤ q k)
    (hpm : ∑ k ∈ s, p k = 1) (hqm : ∑ k ∈ s, q k = 1)
    (hov : δ ≤ ∑ k ∈ s.filter G, min (p k) (q k))
    (hpbad : ∑ k ∈ s.filter (fun k => ¬ G k), p k ≤ η)
    (hqbad : ∑ k ∈ s.filter (fun k => ¬ G k), q k ≤ η)
    (hfband : ∀ k ∈ s.filter G, lo ≤ f k ∧ f k ≤ lo + W) (hW : 0 ≤ W)
    (hfbd : ∀ k ∈ s, |f k| ≤ M) (hlo : |lo| ≤ M) (hη : 0 ≤ η) :
    |∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k| ≤ (1 - δ) * W + 3 * η * M := by
  classical
  set sg := s.filter G with hsg
  set sb := s.filter (fun k => ¬ G k) with hsb
  have hMnn : 0 ≤ M := le_trans (abs_nonneg lo) hlo
  -- split each sum over `s` into the good and bad parts
  have hsplit : ∀ g : ℕ → ℝ, ∑ k ∈ s, g k * f k
      = (∑ k ∈ sg, g k * f k) + ∑ k ∈ sb, g k * f k := by
    intro g
    rw [hsg, hsb, Finset.sum_filter_add_sum_filter_not s G (fun k => g k * f k)]
  rw [hsplit p, hsplit q]
  -- bad-part bound: |∑_bad g·f| ≤ η·M
  have hbad : ∀ g : ℕ → ℝ, (∀ k ∈ s, 0 ≤ g k) → (∑ k ∈ sb, g k ≤ η) →
      |∑ k ∈ sb, g k * f k| ≤ η * M := by
    intro g hgnn hgη
    have hsubset : sb ⊆ s := by rw [hsb]; exact Finset.filter_subset _ _
    calc |∑ k ∈ sb, g k * f k| ≤ ∑ k ∈ sb, |g k * f k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ sb, g k * |f k| := by
          apply Finset.sum_congr rfl; intro k hk
          rw [abs_mul, abs_of_nonneg (hgnn k (hsubset hk))]
      _ ≤ ∑ k ∈ sb, g k * M := by
          apply Finset.sum_le_sum; intro k hk
          exact mul_le_mul_of_nonneg_left (hfbd k (hsubset hk)) (hgnn k (hsubset hk))
      _ = (∑ k ∈ sb, g k) * M := by rw [Finset.sum_mul]
      _ ≤ η * M := mul_le_mul_of_nonneg_right hgη hMnn
  have hbadp := hbad p hpnn hpbad
  have hbadq := hbad q hqnn hqbad
  -- good-part bound: |∑_good p·f − ∑_good q·f| ≤ (1−δ)·W + η·M
  set r : ℕ → ℝ := fun k => min (p k) (q k) with hr
  have hgnn_p : ∀ k ∈ sg, 0 ≤ p k := fun k hk => hpnn k (Finset.filter_subset _ _ hk)
  have hgnn_q : ∀ k ∈ sg, 0 ≤ q k := fun k hk => hqnn k (Finset.filter_subset _ _ hk)
  have hpr : ∀ k ∈ sg, 0 ≤ p k - r k := fun k _ => by
    simp only [hr]; linarith [min_le_left (p k) (q k)]
  have hqr : ∀ k ∈ sg, 0 ≤ q k - r k := fun k _ => by
    simp only [hr]; linarith [min_le_right (p k) (q k)]
  set mp := ∑ k ∈ sg, p k with hmp
  set mq := ∑ k ∈ sg, q k with hmq
  set ρ := ∑ k ∈ sg, r k with hρ
  have hmp1 : mp ≤ 1 := by
    rw [hmp]; calc ∑ k ∈ sg, p k ≤ ∑ k ∈ s, p k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk _ => hpnn k hk)
      _ = 1 := hpm
  have hmq1 : mq ≤ 1 := by
    rw [hmq]; calc ∑ k ∈ sg, q k ≤ ∑ k ∈ s, q k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk _ => hqnn k hk)
      _ = 1 := hqm
  have hρδ : δ ≤ ρ := by rw [hρ, hr]; exact hov
  -- `r = min p q` cancels in the difference of good averages
  set Sp := ∑ k ∈ sg, (p k - r k) * f k with hSp
  set Sq := ∑ k ∈ sg, (q k - r k) * f k with hSq
  have hcancel : (∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k) = Sp - Sq := by
    rw [hSp, hSq, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have hmass_pr : ∑ k ∈ sg, (p k - r k) = mp - ρ := by
    rw [Finset.sum_sub_distrib, ← hmp, ← hρ]
  have hmass_qr : ∑ k ∈ sg, (q k - r k) = mq - ρ := by
    rw [Finset.sum_sub_distrib, ← hmq, ← hρ]
  -- bracket each good sub-average between `mass·lo` and `mass·lo + mass·W`
  have hSp_lo : (mp - ρ) * lo ≤ Sp := by
    rw [hSp, ← hmass_pr, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).1 (hpr k hk))
  have hSp_hi : Sp ≤ (mp - ρ) * lo + (mp - ρ) * W := by
    calc Sp ≤ ∑ k ∈ sg, (p k - r k) * (lo + W) := by
          rw [hSp]; exact Finset.sum_le_sum
            (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).2 (hpr k hk))
      _ = (mp - ρ) * (lo + W) := by rw [← Finset.sum_mul, hmass_pr]
      _ = (mp - ρ) * lo + (mp - ρ) * W := by ring
  have hSq_lo : (mq - ρ) * lo ≤ Sq := by
    rw [hSq, ← hmass_qr, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).1 (hqr k hk))
  have hSq_hi : Sq ≤ (mq - ρ) * lo + (mq - ρ) * W := by
    calc Sq ≤ ∑ k ∈ sg, (q k - r k) * (lo + W) := by
          rw [hSq]; exact Finset.sum_le_sum
            (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).2 (hqr k hk))
      _ = (mq - ρ) * (lo + W) := by rw [← Finset.sum_mul, hmass_qr]
      _ = (mq - ρ) * lo + (mq - ρ) * W := by ring
  have hPW : (mp - ρ) * W ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  have hQW : (mq - ρ) * W ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  -- |mp − mq| ≤ η  (each good mass is 1 minus its bad mass, both bad masses in [0, η])
  have hpgood_split : mp + ∑ k ∈ sb, p k = 1 := by
    rw [hmp, hsg, hsb, Finset.sum_filter_add_sum_filter_not s G p, hpm]
  have hqgood_split : mq + ∑ k ∈ sb, q k = 1 := by
    rw [hmq, hsg, hsb, Finset.sum_filter_add_sum_filter_not s G q, hqm]
  have hpbnn : 0 ≤ ∑ k ∈ sb, p k :=
    Finset.sum_nonneg (fun k hk => hpnn k (Finset.filter_subset _ _ hk))
  have hqbnn : 0 ≤ ∑ k ∈ sb, q k :=
    Finset.sum_nonneg (fun k hk => hqnn k (Finset.filter_subset _ _ hk))
  have hmpmq : |mp - mq| ≤ η := by
    have h1 : mp - mq = (∑ k ∈ sb, q k) - (∑ k ∈ sb, p k) := by linarith
    rw [h1, abs_le]; constructor <;> linarith
  have hPLQL : |(mp - ρ) * lo - (mq - ρ) * lo| ≤ η * M := by
    have heq : (mp - ρ) * lo - (mq - ρ) * lo = (mp - mq) * lo := by ring
    rw [heq, abs_mul]
    exact mul_le_mul hmpmq hlo (abs_nonneg lo) hη
  rw [abs_le] at hPLQL
  have hgood : |(∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k)| ≤ (1 - δ) * W + η * M := by
    rw [hcancel, abs_le]
    constructor
    · linarith [hSp_lo, hSp_hi, hSq_lo, hSq_hi, hPW, hQW, hPLQL.1, hPLQL.2]
    · linarith [hSp_lo, hSp_hi, hSq_lo, hSq_hi, hPW, hQW, hPLQL.1, hPLQL.2]
  -- bad difference bound
  have hbd2 : |(∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k)| ≤ η * M + η * M := by
    have h := abs_add_le (∑ k ∈ sb, p k * f k) (-(∑ k ∈ sb, q k * f k))
    rw [← sub_eq_add_neg, abs_neg] at h
    linarith [hbadp, hbadq]
  -- combine good + bad
  calc |(∑ k ∈ sg, p k * f k + ∑ k ∈ sb, p k * f k)
          - (∑ k ∈ sg, q k * f k + ∑ k ∈ sb, q k * f k)|
      = |((∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k))
          + ((∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k))| := by congr 1; ring
    _ ≤ |(∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k)|
          + |(∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k)| := abs_add_le _ _
    _ ≤ ((1 - δ) * W + η * M) + (η * M + η * M) := by linarith [hgood, hbd2]
    _ = (1 - δ) * W + 3 * η * M := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 cover: reusable summability of the per-scale defect bound

The Erdős record-cover assembly accumulates one-step pullback losses
`Δ_N = (|boundaryTerm N| + M·|kernelMass N − 1| + M·R_N)/μ` along a chain of running-max
predecessors whose `√N` strictly decreases by a fixed amount per step.  Summing the losses over
that `√`-spaced chain converges because, as a function of the scale `t = √N`, each piece of `Δ`
is summable in `t`:

* `|boundaryTerm N| ≤ σ(N)·e^{−C√N} ≤ N²·e^{−Ct} = t⁴·e^{−Ct}` — polynomial × exponential decay,
* `M·R_N = M·N³·e^{−(C/10)√N} = M·t⁶·e^{−(C/10)t}` — polynomial × exponential decay,
* `M·|kernelMass N − 1| ≤ M·K/N = M·K/t²` — inverse-square.

This file proves the two chain-independent summability building blocks (`Σ tᵏ e^{−ct}` and
`Σ 1/(t+1)²`) and their sum.  The chain-dependent bookkeeping (how the `Δ`'s are indexed by the
`√`-spaced chain) lives in the cover-assembly file.  Opus-authored.
-/

noncomputable section

open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_t tᵏ · e^{−c t}` converges for `c > 0`: polynomial times geometric. -/
lemma summable_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun t : ℕ => (t : ℝ) ^ k * Real.exp (-c * (t : ℝ))) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-c) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hsum := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr
  refine hsum.congr (fun t => ?_)
  rw [← Real.exp_nat_mul, mul_comm (t : ℝ) (-c)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 renewal route: well-founded `Hit`/`Pot` potentials

The banked spine lemmas (`rec_iter_bound`, `pot_le_block_sum_of_leave`) take the `Hit`/`Pot`
fixed-point equations as hypotheses.  This file constructs the actual functions by well-founded
recursion on `n` (the kernel `P n k` is summed over `Finset.range n`, so every recursive call is on
`k < n`).  We sum over `(Finset.range n).attach` so each summand carries the membership proof
`k ∈ range n` (hence `k < n`) needed for termination, then recover the plain-`range` defining
equations via `Finset.sum_attach`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma hitVal_eq (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (φ : ℕ → ℝ) (n : ℕ) :
    hitVal P rank J φ n
      = if rank n < J then φ n
        else ∑ k ∈ Finset.range n, P n k * hitVal P rank J φ k := by
  rw [hitVal]
  by_cases h : rank n < J
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * hitVal P rank J φ k)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma kernelMass_nonneg (n : ℕ) : 0 ≤ kernelMass n :=
  Finset.sum_nonneg (fun _ hm => erdosWeight_nonneg_of_mem hm)

lemma Pker_nonneg (n k : ℕ) : 0 ≤ Pker n k := by
  unfold Pker
  split_ifs with h
  · exact div_nonneg (erdosWeight_nonneg_of_lt (by omega)) (kernelMass_nonneg n)
  · exact le_refl 0

lemma rnk_mono : Monotone rnk := by
  intro a b hab
  apply Nat.floor_mono
  have : Real.sqrt (a : ℝ) ≤ Real.sqrt (b : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hab)
  linarith

/-- Reflection `k ↦ n−k` on `Icc 1 (n−1)`. -/
lemma sum_Icc_reflect_sub (n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (n - 1), F (n - k) = ∑ m ∈ Finset.Icc 1 (n - 1), F m := by
  apply Finset.sum_nbij' (fun k => n - k) (fun m => n - m)
  · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro k hk; rw [Finset.mem_Icc] at hk; omega
  · intro m hm; rw [Finset.mem_Icc] at hm; omega
  · intro k _; rfl

/-- Folding the normalized kernel against any test function `φ`, reindexed to the step variable. -/
lemma Pker_sum_mul (n : ℕ) (hn : 2 ≤ n) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, Pker n k * φ k
      = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * φ (n - m)) / kernelMass n := by
  have hsub : ∑ k ∈ Finset.range n, Pker n k * φ k
      = ∑ k ∈ Finset.Icc 1 (n - 1), Pker n k * φ k := by
    symm
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k _ hknot
      rw [Finset.mem_Icc] at hknot
      have hP0 : Pker n k = 0 := by
        unfold Pker; rw [if_neg]; rintro ⟨h1, h2⟩; omega
      rw [hP0, zero_mul]
  rw [hsub]
  have hval : ∀ k ∈ Finset.Icc 1 (n - 1),
      Pker n k * φ k = erdosWeight n (n - k) * φ k / kernelMass n := by
    intro k hk; rw [Finset.mem_Icc] at hk
    unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]; ring
  rw [Finset.sum_congr rfl hval, ← Finset.sum_div]
  congr 1
  rw [← sum_Icc_reflect_sub n (fun j => erdosWeight n j * φ (n - j))]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_Icc] at hk
  rw [show n - (n - k) = k by omega]

/-- **Probability normalization** (`hP_mass`): the normalized kernel sums to `1`. -/
lemma Pker_mass {n : ℕ} (hn : 2 ≤ n) (hS : kernelMass n ≠ 0) :
    ∑ k ∈ Finset.range n, Pker n k = 1 := by
  have h := Pker_sum_mul n hn (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  rw [show (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m) = kernelMass n from rfl]
  exact div_self hS

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- `rnk n ≥ 3·n₀+3` forces `n ≥ n₀` (converts eventual-in-`n` facts into `J ≤ rnk n` form). -/
lemma rnk_ge_of {n₀ n : ℕ} (h : 3 * n₀ + 3 ≤ rnk n) : n₀ ≤ n := by
  have h1 := (rnk_sqrt_bounds n).1
  have hge : (n₀ : ℝ) + 1 ≤ Real.sqrt n := by
    have hcast : (3 * n₀ + 3 : ℝ) ≤ (rnk n : ℝ) := by exact_mod_cast h
    have : (3 * (n₀ : ℝ) + 3) ≤ 3 * Real.sqrt n := by push_cast at hcast ⊢; linarith
    linarith
  have hsq : ((n₀ : ℝ) + 1) ^ 2 ≤ (n : ℝ) := by
    have hmul := mul_le_mul hge hge (by positivity) (Real.sqrt_nonneg _)
    rw [← pow_two, ← pow_two, Real.sq_sqrt (by positivity)] at hmul
    exact hmul
  have : (n₀ : ℝ) ≤ (n : ℝ) := by nlinarith [hsq]
  exact_mod_cast this

/-- The fixed window `(√n, 2√n]` carries a uniform positive kernel mass (the `a₀=1` instance of
`erdos_kernel_fixed_window_pos`, exposed explicitly so window steps `m>√n` apply `window_rank_drop`). -/
lemma kernelWindow_one_two_pos :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᶠ n : ℕ in atTop, ν ≤ kernelWindow 1 2 n := by
  have hC := C_pos
  have hIpos : 0 < Model.modelIntegral C 1 2 := by
    rw [Model.modelIntegral]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
        have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
          continuous_const.mul continuous_id
        have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact h1.mul h2
      exact hc.intervalIntegrable _ _
    · intro y hy
      have hy1 : (1 : ℝ) < y := hy.1
      have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
      have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
      nlinarith [mul_pos (mul_pos hπ (by linarith : (0:ℝ) < y)) he]
    · norm_num
  refine ⟨Model.modelIntegral C 1 2 / 2, by positivity, ?_⟩
  have hwin := Model.erdos_kernel_window (a := 1) (b := 2) zero_le_one one_lt_two
  have hev := (tendsto_order.1 hwin).1 (Model.modelIntegral C 1 2 / 2) (by linarith)
  filter_upwards [hev] with n hn
  exact hn.le

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: concrete facts about `rnk` and `kernelMass`

Two elementary facts needed to instantiate the abstract `tendsto_of_killed_doeblin` for the concrete
Erdős predecessor kernel: the rank map `rnk n = ⌊3√n⌋` diverges (`rnk → atTop`), and the kernel mass
`kernelMass n` is eventually strictly positive (it dominates the window mass, which is `≥ ν > 0`
eventually).  The latter makes `Pker` row-stochastic for large `n` (via `Pker_mass`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank map diverges: `rnk n = ⌊3√n⌋ → ∞`. -/
lemma rnk_tendsto_atTop : Tendsto rnk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨(b + 1) ^ 2, fun n hn => ?_⟩
  have h1 : ((b + 1) ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb_le_sqrt : (b : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (b : ℝ) = Real.sqrt ((b : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [h1, (Nat.cast_nonneg b : (0:ℝ) ≤ (b:ℝ))]
  have hsqrt : (b : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
    have := Real.sqrt_nonneg (n : ℝ); linarith
  unfold rnk
  exact Nat.le_floor hsqrt

/-- The kernel mass is eventually strictly positive (it dominates the positive window mass). -/
lemma kernelMass_pos_eventually : ∀ᶠ n : ℕ in atTop, 0 < kernelMass n := by
  obtain ⟨ν, hν, hwin⟩ := kernelWindow_one_two_pos
  filter_upwards [hwin] with n hn
  have hle : kernelWindow 1 2 n ≤ kernelMass n := by
    unfold kernelWindow kernelMass
    apply Finset.sum_le_sum
    intro m hm
    split
    · exact le_refl _
    · exact erdosWeight_nonneg_of_mem hm
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: boundedness of `hitVal` and substochasticity of `Pker`

The hitting value `hitVal P rank J φ` is a sub-convex combination of boundary values of `φ`, so it
inherits `φ`'s bound: if `φ` is globally bounded by `Mφ`, `P` is nonnegative and substochastic above the
cutoff, then `|hitVal P rank J φ n| ≤ Mφ` for all `n` (strong induction on the predecessor recursion).
The concrete predecessor kernel `Pker` is substochastic (`∑_{k<n} Pker n k ≤ 1`): the row mass is `1`
when `kernelMass n ≠ 0` and `0` otherwise.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Pker` is substochastic: each row sums to at most `1`. -/
lemma Pker_sum_le_one (n : ℕ) : ∑ k ∈ Finset.range n, Pker n k ≤ 1 := by
  by_cases hn : 2 ≤ n
  · by_cases hkm : kernelMass n = 0
    · have hz : ∀ k ∈ Finset.range n, Pker n k = 0 := by
        intro k _; unfold Pker; split
        · rw [hkm, div_zero]
        · rfl
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num
    · exact le_of_eq (Pker_mass hn hkm)
  · have hz : ∀ k ∈ Finset.range n, Pker n k = 0 := by
      intro k hk; rw [Finset.mem_range] at hk; unfold Pker; rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ} {φ : ℕ → ℝ}

/-- A globally bounded boundary `φ` makes the hitting value bounded by the same constant. -/
lemma hitVal_abs_le {Mφ : ℝ} (hMφ0 : 0 ≤ Mφ) (hφ : ∀ m, |φ m| ≤ Mφ)
    (hPnn : ∀ n k, 0 ≤ P n k)
    (hsub : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k ≤ 1) :
    ∀ n, |hitVal P rank J φ n| ≤ Mφ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hitVal_eq]
    by_cases hb : rank n < J
    · rw [if_pos hb]; exact hφ n
    · rw [if_neg hb]
      have hJ : J ≤ rank n := not_lt.mp hb
      calc |∑ k ∈ Finset.range n, P n k * hitVal P rank J φ k|
          ≤ ∑ k ∈ Finset.range n, |P n k * hitVal P rank J φ k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n, P n k * |hitVal P rank J φ k| := by
            apply Finset.sum_congr rfl; intro k _
            rw [abs_mul, abs_of_nonneg (hPnn n k)]
        _ ≤ ∑ k ∈ Finset.range n, P n k * Mφ := by
            apply Finset.sum_le_sum; intro k hk
            rw [Finset.mem_range] at hk
            exact mul_le_mul_of_nonneg_left (ih k hk) (hPnn n k)
        _ = (∑ k ∈ Finset.range n, P n k) * Mφ := by rw [Finset.sum_mul]
        _ ≤ 1 * Mφ := mul_le_mul_of_nonneg_right (hsub n hJ) hMφ0
        _ = Mφ := one_mul _

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin (File C): the oscillation→0 engine

`L`-step geometric contraction with vanishing forcing drives a bounded nonnegative sequence to `0`:
`W(n+L) ≤ q·W(n) + e_n` with `0 ≤ q < 1`, `e_n → 0` ⟹ `W → 0`.  The forcing need only vanish, not be
summable — the geometric factor `q < 1` beats it.  Proof by an `ε`–`N` limsup argument.  This is the
convergence driver for the Doeblin block-oscillation contraction.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Variable-step contraction (antitone form).**  When `W` is antitone and bounded below by `0`, a
geometric contraction `W(R + A R) ≤ q·W R + e R` with `0 ≤ q < 1`, `e → 0` and `A R → ∞` (so the
contraction couples `W` to its own tail at `R + A R → ∞`) forces `W → 0`.  Much easier than the
fixed-step limsup argument: an antitone `W ≥ 0` converges to `ℓ := ⨅ W ≥ 0`, both sides of the
recursion tend to limits, and passing to the limit gives `ℓ ≤ q·ℓ`, hence `ℓ = 0`. -/
theorem tendsto_zero_of_variable_step_contraction
    {W e : ℕ → ℝ} {q : ℝ} {A : ℕ → ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hWnn : ∀ R, 0 ≤ W R) (hWbd : BddAbove (Set.range W))
    (hWmono : Antitone W)
    (hApos : ∀ᶠ R in atTop, 1 ≤ A R)
    (hAunbounded : Tendsto A atTop atTop)
    (hAsublinear : ∀ᶠ R in atTop, A R ≤ R / 2)
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ᶠ R in atTop, W (R + A R) ≤ q * W R + e R) :
    Tendsto W atTop (𝓝 0) := by
  -- `W` antitone, bounded below by `0` ⟹ converges to `ℓ := ⨅ W ≥ 0`.
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  set ℓ : ℝ := ⨅ R, W R with hℓ
  have hWtend : Tendsto W atTop (𝓝 ℓ) := tendsto_atTop_ciInf hWmono hBB
  -- `ℓ ≥ 0` (infimum of nonnegatives).
  have hℓnn : 0 ≤ ℓ := le_ciInf (fun R => hWnn R)
  -- `R + A R → ∞`, since `A ≥ 0`, so `R ≤ R + A R`.
  have hshiftTop : Tendsto (fun R => R + A R) atTop atTop :=
    tendsto_atTop_mono (fun R => Nat.le_add_right R (A R)) tendsto_id
  -- Hence `W (R + A R) → ℓ` (compose the convergent `W` with `R + A R → ∞`).
  have hWshift : Tendsto (fun R => W (R + A R)) atTop (𝓝 ℓ) := hWtend.comp hshiftTop
  -- RHS `q·W R + e R → q·ℓ + 0 = q·ℓ`.
  have hRHS : Tendsto (fun R => q * W R + e R) atTop (𝓝 (q * ℓ)) := by
    have h1 : Tendsto (fun R => q * W R) atTop (𝓝 (q * ℓ)) := hWtend.const_mul q
    simpa using h1.add he
  -- Pass to the limit in `W (R + A R) ≤ q·W R + e R`: `ℓ ≤ q·ℓ`.
  have hℓle : ℓ ≤ q * ℓ := le_of_tendsto_of_tendsto hWshift hRHS hrec
  -- `(1 − q)·ℓ ≤ 0`, `1 − q > 0`, `ℓ ≥ 0` ⟹ `ℓ = 0`.
  have hℓ0 : ℓ = 0 := by nlinarith [hℓnn, hℓle, hq1]
  rwa [hℓ0] at hWtend

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the tail band (sup/inf over a rank tail)

For a bounded `h` and a rank map `rank → atTop`, the *tail band* at level `R` is `[d R, D R]` where
`D R = sSup (h '' {k | rank k ≥ R})` and `d R = sInf (…)`.  Its width `V R = D R − d R` is the tail
oscillation: antitone in `R`, nonnegative, `≤ 2M`, and dominates every pairwise difference
`|h i − h j|` with `rank i, rank j ≥ R`.  Every `h k` with `rank k ≥ R` lies in `[d R, d R + V R]`.
This supplies the `lo = d`, `W = V` band and the oscillation dominator for the Doeblin escape
contraction.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank tail `{k | R ≤ rank k}`. -/
def tailSet (rank : ℕ → ℕ) (R : ℕ) : Set ℕ := {k | R ≤ rank k}

/-- Tail supremum of `h` over `{rank ≥ R}`. -/
def tailSup (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := sSup (h '' tailSet rank R)

/-- Tail infimum of `h` over `{rank ≥ R}`. -/
def tailInf (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := sInf (h '' tailSet rank R)

/-- Tail oscillation (band width). -/
def tailOsc (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := tailSup h rank R - tailInf h rank R

variable {h : ℕ → ℝ} {rank : ℕ → ℕ} {M : ℝ}

lemma tailSet_nonempty (hrank : Tendsto rank atTop atTop) (R : ℕ) :
    (h '' tailSet rank R).Nonempty := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
  exact ⟨h N, N, hN N le_rfl, rfl⟩

lemma tail_bddAbove (hM : ∀ n, |h n| ≤ M) (R : ℕ) : BddAbove (h '' tailSet rank R) :=
  ⟨M, by rintro _ ⟨k, _, rfl⟩; exact le_trans (le_abs_self _) (hM k)⟩

lemma tail_bddBelow (hM : ∀ n, |h n| ≤ M) (R : ℕ) : BddBelow (h '' tailSet rank R) :=
  ⟨-M, by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _)⟩

/-- Every tail value sits between `d R` and `D R`. -/
lemma tail_band (hM : ∀ n, |h n| ≤ M) {R k : ℕ} (hk : R ≤ rank k) :
    tailInf h rank R ≤ h k ∧ h k ≤ tailSup h rank R := by
  have hmem : h k ∈ h '' tailSet rank R := ⟨k, hk, rfl⟩
  exact ⟨csInf_le (tail_bddBelow hM R) hmem, le_csSup (tail_bddAbove hM R) hmem⟩

/-- `|h i − h j| ≤ V R` for both ranks `≥ R`. -/
lemma tailOsc_abs_le (hM : ∀ n, |h n| ≤ M) {R i j : ℕ}
    (hi : R ≤ rank i) (hj : R ≤ rank j) : |h i - h j| ≤ tailOsc h rank R := by
  rw [tailOsc, abs_le]
  obtain ⟨hil, hiu⟩ := tail_band (rank := rank) hM hi
  obtain ⟨hjl, hju⟩ := tail_band (rank := rank) hM hj
  constructor <;> linarith

lemma tailOsc_nonneg (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    0 ≤ tailOsc h rank R := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
  have := tailOsc_abs_le (rank := rank) hM (i := N) (j := N) (hN N le_rfl) (hN N le_rfl)
  simpa using (abs_nonneg _).trans this

lemma tailOsc_le_two_M (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    tailOsc h rank R ≤ 2 * M := by
  have hsup : tailSup h rank R ≤ M :=
    csSup_le (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (le_abs_self _) (hM k))
  have hinf : -M ≤ tailInf h rank R :=
    le_csInf (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _))
  rw [tailOsc]; linarith

lemma tailInf_abs_le (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    |tailInf h rank R| ≤ M := by
  rw [abs_le]
  have hinf_ge : -M ≤ tailInf h rank R :=
    le_csInf (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _))
  have hinf_le : tailInf h rank R ≤ M := by
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
    exact le_trans (csInf_le (tail_bddBelow hM R) ⟨N, hN N le_rfl, rfl⟩)
      (le_trans (le_abs_self _) (hM N))
  exact ⟨hinf_ge, hinf_le⟩

/-- `V` is antitone: a deeper tail has larger oscillation. -/
lemma tailOsc_antitone (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M)
    {R R' : ℕ} (hRR : R ≤ R') : tailOsc h rank R' ≤ tailOsc h rank R := by
  have himg : h '' tailSet rank R' ⊆ h '' tailSet rank R :=
    Set.image_mono (fun k hk => le_trans hRR hk)
  have hne' : (h '' tailSet rank R').Nonempty := tailSet_nonempty (h := h) hrank R'
  have hsup : tailSup h rank R' ≤ tailSup h rank R :=
    csSup_le_csSup (tail_bddAbove hM R) hne' himg
  have hinf : tailInf h rank R ≤ tailInf h rank R' :=
    csInf_le_csInf (tail_bddBelow hM R) hne' himg
  rw [tailOsc, tailOsc]; linarith

/-- Upper bound on the tail oscillation from a uniform pairwise bound. -/
lemma tailOsc_le_of_pairwise (hrank : Tendsto rank atTop atTop) {R : ℕ} {X : ℝ}
    (hpair : ∀ i j, R ≤ rank i → R ≤ rank j → h i - h j ≤ X) :
    tailOsc h rank R ≤ X := by
  have hne := tailSet_nonempty (h := h) hrank R
  have key : tailSup h rank R ≤ X + tailInf h rank R := by
    rw [tailSup]
    refine csSup_le hne ?_
    rintro _ ⟨i, hi, rfl⟩
    have hiR : R ≤ rank i := hi
    have hle : h i - X ≤ tailInf h rank R := by
      rw [tailInf]
      refine le_csInf hne ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjR : R ≤ rank j := hj
      linarith [hpair i j hiR hjR]
    linarith
  rw [tailOsc]; linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: tail-oscillation → 0 ⟹ convergence

The final abstract closer of the §9 route.  If a sequence `h` has a *tail-oscillation* dominator `V`
— `|h i − h j| ≤ V R` whenever both `rank i, rank j ≥ R` — and `V → 0`, then `h` is Cauchy along the
filter `rank → atTop`, hence converges.  This is the kernel-free endgame: the Doeblin/escape analysis
only has to drive the single scalar sequence `V` to `0` (via `tendsto_zero_of_step_contraction`), and
this lemma turns that into `∃ L, h → L` — exactly Fact B for `hitVal`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **§9 endgame.** A vanishing tail-oscillation dominator `V` forces `h` to converge. -/
theorem tendsto_of_tail_osc_to_zero {h V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hrank : Tendsto rank atTop atTop)
    (hVtend : Tendsto V atTop (𝓝 0))
    (hVosc : ∀ R i j, R ≤ rank i → R ≤ rank j → |h i - h j| ≤ V R) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  have hcau : CauchySeq h := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- pick a rank cutoff `R` where the tail oscillation is `< ε`
    obtain ⟨R, hR0⟩ := Metric.tendsto_atTop.1 hVtend ε hε
    have hR := hR0 R le_rfl
    have hVR : V R < ε := by
      rw [Real.dist_eq, sub_zero] at hR
      exact lt_of_le_of_lt (le_abs_self _) hR
    -- past some index every term has rank `≥ R`
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hVosc R m n (hN m hm) (hN n hn)) hVR
  exact cauchySeq_tendsto_of_complete hcau

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the connection to `erdos_partition_limit_exists`

Instantiates the abstract `tendsto_of_killed_doeblin` for the concrete Erdős predecessor kernel
`killedKer Pker rnk J`, producing the full reduction:

  if the **Doeblin walls** hold for cofinitely many cutoffs `J` (finite-time overlap `δ > 0` on the
  high-rank band + vanishing escape mass), then the normalized partition sequence `u` converges to a
  positive limit — the existence of the Hardy–Ramanujan constant.

Every step here is mechanical (boundedness of `hitVal`, substochasticity of `Pker`, `rnk → atTop`,
row-stochasticity of the killed kernel for large `J`, the `KPowK L P̃`-harmonic identity); the two walls
bundled in `DoeblinWalls` are the only remaining analytic content (the Γ(2,C) convolution local-limit
wall — see HANDOFF UPDATE 8).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `u` is nonnegative (`n · p(n) · e^{…} ≥ 0`). -/
lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  unfold u
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by unfold part; exact Nat.cast_nonneg _))
    (Real.exp_pos _).le

/-- `u` is globally bounded (eventual `limsup` bound padded by the finitely many initial terms). -/
lemma u_abs_le : ∃ Mu : ℝ, 0 ≤ Mu ∧ ∀ n, |u n| ≤ Mu := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
  refine ⟨max M (∑ k ∈ Finset.range N, |u k|), le_trans hMpos.le (le_max_left _ _), fun n => ?_⟩
  by_cases h : n < N
  · exact le_trans (Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg (u k))
      (Finset.mem_range.mpr h)) (le_max_right _ _)
  · rw [abs_of_nonneg (u_nonneg n)]
    exact le_trans (hN n (by omega)) (le_max_left _ _)

/-- `Pker` is supported on strict predecessors (`n ≤ k → Pker n k = 0`). -/
lemma Pker_supp (n k : ℕ) (h : n ≤ k) : Pker n k = 0 := by
  unfold Pker; rw [if_neg (by omega)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK 11: the first-entrance (run-until-hit) rank-band Doeblin engine

The fixed-step-count overlap reductions (`ErdosAlignment`, `DoeblinWalls`) are *false* for far-apart
high ranks (rank drops by `O(1)` per step, so a rank-`1000R` chain and a rank-`1001R` chain have
disjoint `L`-step laws for any fixed `L`).  This file builds the correct
device: the **first-entrance kernel** `enterBandKer P B`, which runs the chain *until* it enters a
finite rank band `B` — variable hitting time, not a fixed step count.  Two chains starting from very
different heights both descend *through* the band, and their first-entrance laws overlap.

Steps A–D (this file) are deterministic and reuse the banked Doeblin contraction
(`doeblin_average_diff_bound`) and the banked tail-oscillation engine (`tailOsc`,
`tendsto_zero_of_step_contraction`, `tendsto_of_tail_osc_to_zero`); they do **not** depend on the
hard analytic overlap sublemma (Step E).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Step A — the first-entrance kernel -/

/-- Defining equation of `enterBandKer` over the plain `Finset.range n`. -/
lemma enterBandKer_eq (P : ℕ → ℕ → ℝ) (B : Finset ℕ) (n z : ℕ) :
    enterBandKer P B n z
      = if n ∈ B then (if z = n then 1 else 0)
        else ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
  rw [enterBandKer]
  by_cases h : n ∈ B
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * enterBandKer P B k z)]

variable {P : ℕ → ℕ → ℝ} {B : Finset ℕ}

/-- `enterBandKer` is nonnegative (given `P` nonnegative). -/
lemma enterBandKer_nonneg (hPnn : ∀ n k, 0 ≤ P n k) (n z : ℕ) :
    0 ≤ enterBandKer P B n z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [enterBandKer_eq]
    by_cases h : n ∈ B
    · rw [if_pos h]; split <;> norm_num
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun k hk =>
        mul_nonneg (hPnn n k) (ih k (Finset.mem_range.mp hk)))

/-- The total entrance mass over the band is `1`, given the chain is row-stochastic at every off-band
point (`hrow`).  The chain runs until it enters `B`, and every step off `B` conserves mass. -/
lemma enterBandKer_row_sum
    (hrow : ∀ m, m ∉ B → ∑ k ∈ Finset.range m, P m k = 1) (n : ℕ) :
    ∑ z ∈ B, enterBandKer P B n z = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ∈ B
    · -- point mass at n ∈ B
      have : ∀ z, enterBandKer P B n z = if z = n then 1 else 0 := by
        intro z; rw [enterBandKer_eq, if_pos h]
      rw [Finset.sum_congr rfl (fun z _ => this z)]
      rw [Finset.sum_ite_eq' B n (fun _ => (1 : ℝ)), if_pos h]
    · -- one P-step then recurse: ∑_z ∑_k P n k · enter k z = ∑_k P n k · 1 = ∑_k P n k = 1
      have hexpand : ∀ z, enterBandKer P B n z
          = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
        intro z; rw [enterBandKer_eq, if_neg h]
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      have hk : ∀ k ∈ Finset.range n, ∑ z ∈ B, P n k * enterBandKer P B k z = P n k := by
        intro k hk
        rw [← Finset.mul_sum, ih k (Finset.mem_range.mp hk), mul_one]
      rw [Finset.sum_congr rfl hk]
      exact hrow n h

/-! ## Step B — the entrance decomposition for `hitVal` -/

/-- **Entrance decomposition.**  A function harmonic at every off-band point equals its first-entrance
average over the band.  When `B` is the ceiling down-set `{rnk < R+A}` with `R ≥ J`, every off-band
point has rank `≥ R+A ≥ J`, so `hitVal` is harmonic there and `hharm` is discharged. -/
lemma hitVal_eq_enterBand_average {rank : ℕ → ℕ} {J : ℕ} {φ : ℕ → ℝ}
    (hharm : ∀ m, m ∉ B → hitVal P rank J φ m
        = ∑ k ∈ Finset.range m, P m k * hitVal P rank J φ k)
    (n : ℕ) :
    hitVal P rank J φ n = ∑ z ∈ B, enterBandKer P B n z * hitVal P rank J φ z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ∈ B
    · -- enterBandKer is point mass at n; the sum collapses to hitVal n
      have hpt : ∀ z, enterBandKer P B n z * hitVal P rank J φ z
          = if z = n then hitVal P rank J φ n else 0 := by
        intro z; rw [enterBandKer_eq, if_pos h]
        by_cases hz : z = n
        · rw [if_pos hz, if_pos hz, one_mul, hz]
        · rw [if_neg hz, if_neg hz, zero_mul]
      rw [Finset.sum_congr rfl (fun z _ => hpt z)]
      rw [Finset.sum_ite_eq' B n (fun _ => hitVal P rank J φ n), if_pos h]
    · -- harmonic step + recursion: hitVal n = ∑_k P n k hitVal k = ∑_k P n k ∑_z enter k z hitVal z
      rw [hharm n h]
      have hstep : ∀ k ∈ Finset.range n,
          P n k * hitVal P rank J φ k
            = ∑ z ∈ B, P n k * (enterBandKer P B k z * hitVal P rank J φ z) := by
        intro k hk
        rw [ih k (Finset.mem_range.mp hk), Finset.mul_sum]
      rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [enterBandKer_eq (P := P) (B := B) n z, if_neg h, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => by ring)

/-! ## Step C — Doeblin contraction of the entrance average (wires `doeblin_average_diff_bound`) -/

/-! ## Step D — the descending-ceiling band and the abstract engine

The *band* used by the engine is the **finite ceiling down-set** `ceilBand R A` = all states of rank
`< R + A` (truncated to the recursion's finite range).  This set is **unskippable on the way down**
(the chain can only enter it, never jump over it from above), so the first-entrance decomposition
holds with the harmonic hypothesis discharged at every off-band point (rank `≥ R + A ≥ J`).  The
landed point's rank is `< R + A`; the engine then splits the band into the in-band overlap part
`[R, R+A)` and the **overshoot** part `[0, R)`, which carries an escape mass driving the residual
oscillation.  A *fixed* band width `A` leaves a non-vanishing
escape floor (the genuine obstruction). -/

/-- `rnk k < R + A` already forces `k` into the enumeration window, so membership is rank-only. -/
lemma mem_ceilBand_iff {R A k : ℕ} :
    k ∈ ceilBand R A ↔ rnk k < R + A := by
  unfold ceilBand
  rw [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro hlt
  -- rnk k < R+A ⟹ 3√k < R+A ⟹ √k < (R+A)/3 ⟹ k < (R+A)²/9 < (R+A+2)²
  have hfloor : (3 : ℝ) * Real.sqrt (k : ℝ) < (R + A : ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have : (R + A : ℕ) ≤ rnk k := by
      unfold rnk; exact Nat.le_floor (by push_cast; linarith)
    omega
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hsq : (k : ℝ) < ((R + A : ℝ) / 3) ^ 2 := by
    have hsqrtlt : Real.sqrt (k : ℝ) < (R + A : ℝ) / 3 := by linarith
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [Real.sq_sqrt hknn, hsqrtlt, hsqrtnn]
  have hub : ((R + A : ℝ) / 3) ^ 2 ≤ ((R + A + 2) ^ 2 : ℕ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ (R : ℝ) + (A : ℝ) := by positivity
    nlinarith
  have : (k : ℝ) < ((R + A + 2) ^ 2 : ℕ) := lt_of_lt_of_le hsq hub
  exact_mod_cast this

/-- A point **off** the ceiling band has rank `≥ R + A`. -/
lemma not_mem_ceilBand_rank_ge {R A m : ℕ} (hm : m ∉ ceilBand R A) : R + A ≤ rnk m := by
  by_contra hcon
  exact hm (mem_ceilBand_iff.mpr (Nat.not_le.mp hcon))

/-- **Step D′ — variable-band convergence engine.**

The exact analogue of `hitVal_cauchy_of_ceilBand_overlap_escape` with a **growing** band width
`A R` (variable in the floor `R`) instead of a fixed `A`.  The overlap/escape pair is now measured
against the variable ceiling down-set `ceilBand R (A R)`, and the per-band Doeblin contraction
`W(R + A R) ≤ (1−δ)·W R + 3·(e R)·Mφ` (with `W := tailOsc hitVal rnk`, which is antitone) is driven to
`0` by `tendsto_zero_of_variable_step_contraction`.  Everything else mirrors the fixed-A engine
verbatim.  This is the form needed for the renewal-overshoot route, where the escape mass `q(A)` only
vanishes as `A → ∞`. -/
theorem hitVal_cauchy_of_ceilBand_overlap_escape_variable
    {J : ℕ} {φ : ℕ → ℝ} {δ Mφ : ℝ} {e : ℕ → ℝ} (A : ℕ → ℕ)
    (hAunbounded : Tendsto A atTop atTop) (hAsublinear : ∀ᶠ R in atTop, A R ≤ R / 2)
    (hApos : ∀ᶠ R in atTop, 1 ≤ A R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hMφ0 : 0 ≤ Mφ) (hφ : ∀ m, |φ m| ≤ Mφ)
    (he0 : ∀ R, 0 ≤ e R) (hetend : Tendsto e atTop (𝓝 0))
    (hharm : ∀ m, J ≤ rnk m →
        hitVal Pker rnk J φ m = ∑ k ∈ Finset.range m, Pker m k * hitVal Pker rnk J φ k)
    (hkm : ∀ m, J ≤ rnk m → kernelMass m ≠ 0)
    (hoverlap : ∀ᶠ R in atTop, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
        (δ ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
                min (enterBandKer Pker (ceilBand R (A R)) n z)
                    (enterBandKer Pker (ceilBand R (A R)) n' z))
        ∧ (∑ z ∈ (ceilBand R (A R)).filter (fun z => ¬ R ≤ rnk z),
                enterBandKer Pker (ceilBand R (A R)) n z ≤ e R)
        ∧ (∑ z ∈ (ceilBand R (A R)).filter (fun z => ¬ R ≤ rnk z),
                enterBandKer Pker (ceilBand R (A R)) n' z ≤ e R)) :
    ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J φ n) atTop (𝓝 L) := by
  classical
  set h := fun n => hitVal Pker rnk J φ n with hh
  -- `h` is bounded by `Mφ`
  have hM : ∀ n, |h n| ≤ Mφ :=
    hitVal_abs_le hMφ0 hφ (fun n k => Pker_nonneg n k) (fun n _ => Pker_sum_le_one n)
  -- `Pker` support
  have hPsupp : ∀ n k, n ≤ k → Pker n k = 0 := Pker_supp
  -- choose the threshold floor R₁ ≥ J above which the overlap/escape holds
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hoverlap
  set R₁ := max (max R₀ J) 9 with hR₁
  -- pairwise contraction with floor R: h n − h n' ≤ (1−δ)·tailOsc(R) + 3·(e R)·Mφ
  have hpair : ∀ R, R₁ ≤ R → ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
      h n - h n' ≤ (1 - δ) * tailOsc h rnk R + 3 * e R * Mφ := by
    intro R hR n n' hn hn'
    have hRJ : J ≤ R := le_trans (le_trans (le_max_right R₀ J) (le_max_left _ 9)) hR
    have hRR₀ : R₀ ≤ R := le_trans (le_trans (le_max_left R₀ J) (le_max_left _ 9)) hR
    have hR9 : 9 ≤ R := le_trans (le_max_right _ 9) hR
    set Bnd := ceilBand R (A R) with hBnd
    -- harmonicity off the ceiling band (off-band points have rank ≥ R+A R ≥ J)
    have hharmB : ∀ m, m ∉ Bnd → h m = ∑ k ∈ Finset.range m, Pker m k * h k := by
      intro m hm
      have : R + A R ≤ rnk m := not_mem_ceilBand_rank_ge hm
      exact hharm m (le_trans (le_trans hRJ (Nat.le_add_right R (A R))) this)
    -- entrance decompositions
    have hdec_n : h n = ∑ z ∈ Bnd, enterBandKer Pker Bnd n z * h z :=
      hitVal_eq_enterBand_average hharmB n
    have hdec_n' : h n' = ∑ z ∈ Bnd, enterBandKer Pker Bnd n' z * h z :=
      hitVal_eq_enterBand_average hharmB n'
    -- row sums = 1 (off-band points are row-stochastic since rank ≥ J)
    have hrow : ∀ m, m ∉ Bnd → ∑ k ∈ Finset.range m, Pker m k = 1 := by
      intro m hm
      have hmR : R + A R ≤ rnk m := not_mem_ceilBand_rank_ge hm
      have hJm : J ≤ rnk m := le_trans (le_trans hRJ (Nat.le_add_right R (A R))) hmR
      have h9m : (9 : ℕ) ≤ rnk m := le_trans hR9 (le_trans (Nat.le_add_right R (A R)) hmR)
      have hge : (2 : ℕ) ≤ m := rnk_ge_of (by omega : 3 * 2 + 3 ≤ rnk m)
      exact Pker_mass hge (hkm m hJm)
    have hrn : ∑ z ∈ Bnd, enterBandKer Pker Bnd n z = 1 := enterBandKer_row_sum hrow n
    have hrn' : ∑ z ∈ Bnd, enterBandKer Pker Bnd n' z = 1 := enterBandKer_row_sum hrow n'
    -- overlap + escape facts
    obtain ⟨hov, hbad_n, hbad_n'⟩ := hR₀ R hRR₀ n n' hn hn'
    -- band values of h lie in [tailInf(R), tailInf(R)+tailOsc(R)] on the in-band good part
    have hfband : ∀ z ∈ Bnd.filter (fun z => R ≤ rnk z),
        tailInf h rnk R ≤ h z ∧ h z ≤ tailInf h rnk R + tailOsc h rnk R := by
      intro z hz
      have hzR : R ≤ rnk z := (Finset.mem_filter.mp hz).2
      obtain ⟨hb1, hb2⟩ := tail_band hM hzR
      exact ⟨hb1, by rw [tailOsc]; linarith⟩
    -- apply the escape-split Doeblin contraction
    have hdoeb := doeblin_escape_bound (s := Bnd)
      (p := enterBandKer Pker Bnd n) (q := enterBandKer Pker Bnd n') (f := h)
      (δ := δ) (η := e R) (lo := tailInf h rnk R) (W := tailOsc h rnk R) (M := Mφ)
      (fun z => R ≤ rnk z)
      (fun z _ => enterBandKer_nonneg (fun a b => Pker_nonneg a b) n z)
      (fun z _ => enterBandKer_nonneg (fun a b => Pker_nonneg a b) n' z)
      hrn hrn' hov hbad_n hbad_n' hfband
      (tailOsc_nonneg rnk_tendsto_atTop hM R) (fun z _ => hM z)
      (tailInf_abs_le rnk_tendsto_atTop hM R) (he0 R)
    rw [← hdec_n, ← hdec_n'] at hdoeb
    calc h n - h n' ≤ |h n - h n'| := le_abs_self _
      _ ≤ (1 - δ) * tailOsc h rnk R + 3 * e R * Mφ := hdoeb
  -- lift to the tail-oscillation step contraction: W(R + A R) ≤ (1−δ)·W R + 3·(e R)·Mφ
  have hVcontract : ∀ R, R₁ ≤ R →
      tailOsc h rnk (R + A R) ≤ (1 - δ) * tailOsc h rnk R + 3 * e R * Mφ := by
    intro R hR
    refine tailOsc_le_of_pairwise rnk_tendsto_atTop (fun n n' hn hn' => ?_)
    exact hpair R hR n n' hn hn'
  -- drive the tail oscillation to zero (forcing 3·e·Mφ → 0; geometric factor 1−δ < 1)
  have he_step : Tendsto (fun n => 3 * e n * Mφ) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 3 * e n * Mφ) atTop (𝓝 (3 * 0 * Mφ)) :=
      (hetend.const_mul 3).mul_const Mφ
    simpa using h2
  have hWnn : ∀ n, 0 ≤ tailOsc h rnk n := fun n => tailOsc_nonneg rnk_tendsto_atTop hM n
  have hWbd : BddAbove (Set.range (fun R => tailOsc h rnk R)) :=
    ⟨2 * Mφ, by rintro _ ⟨n, rfl⟩; exact tailOsc_le_two_M rnk_tendsto_atTop hM n⟩
  -- W := tailOsc is antitone (deeper tail ⟹ larger oscillation)
  have hWmono : Antitone (fun R => tailOsc h rnk R) := fun R R' hRR' =>
    tailOsc_antitone rnk_tendsto_atTop hM hRR'
  -- variable-step recursion eventually holds (floor ≥ R₁)
  have hrec : ∀ᶠ R in atTop,
      tailOsc h rnk (R + A R) ≤ (1 - δ) * tailOsc h rnk R + 3 * e R * Mφ := by
    filter_upwards [eventually_ge_atTop R₁] with R hR
    exact hVcontract R hR
  -- nonnegativity of the forcing (needed for the variable driver shape, harmless here)
  have hWtend : Tendsto (fun R => tailOsc h rnk R) atTop (𝓝 0) :=
    tendsto_zero_of_variable_step_contraction (q := 1 - δ) (A := A)
      (by linarith) (by linarith) hWnn hWbd hWmono hApos hAunbounded hAsublinear he_step hrec
  exact tendsto_of_tail_osc_to_zero rnk_tendsto_atTop hWtend
    (fun R i j hi hj => tailOsc_abs_le hM hi hj)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK T2-ceiling, L2: factoring entrance through the ceiling level

The ceiling-level regeneration route factors the first-entrance law into the growing band
`B = ceilBand R (A R)` (the down-set `{rnk < C}`, `C = R + A R`) through the **ceiling level**
`L = {rnk = C}`.  The chain from a high start `n` (`rnk n ≥ C`) descends; the first time it reaches
the *larger* set `ceilBand C 1 = {rnk ≤ C}` it lands either at the ceiling level `L` (`rnk = C`) or
*overshoots* directly into `B` (`rnk < C`).  Keeping only the level-`L` landings gives the
inequality this file proves:

  `∑_{x ∈ L} enterBandKer Pker (ceilBand C 1) n x · enterBandKer Pker B x z
      ≤ enterBandKer Pker B n z`.

The engine consumes this to write the full entrance law from `n` as a *mixture* over ceiling-level
states (weights `a x = enterBandKer Pker (ceilBand C 1) n x`, continuation kernel
`K x = enterBandKer Pker B x`), feeding the mixture-overlap bridge `L1`.

The work is the **first-entrance tower identity** `enterBandKer_tower`: for `B ⊆ B'`,
`enterBandKer P B n z = ∑_{x ∈ B'} enterBandKer P B' n x · enterBandKer P B x z`
(strong Markov at the first hit of `B'`).  Restricting the `x`-sum from `B' = ceilBand C 1` to the
level `L ⊆ B'` and discarding the nonnegative overshoot terms gives L2.

NEW file; imports the banked entrance kernel, does not modify it.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {P : ℕ → ℕ → ℝ}

/-- **First-entrance tower identity.**  If `B ⊆ B'` and `P` is a strict predecessor kernel
(`P m k = 0` for `k ≥ m`), then entering the smaller band `B` factors through the first hit of the
larger band `B'`:

  `enterBandKer P B n z = ∑_{x ∈ B'} enterBandKer P B' n x · enterBandKer P B x z`.

Strong Markov property at the first entrance time of `B'`.  Proved by strong induction on `n`:
if `n ∈ B'` the first hit is `n` itself (point mass) and the sum collapses; otherwise one `P`-step
plus the inductive hypothesis at every predecessor `k < n`. -/
lemma enterBandKer_tower {B B' : Finset ℕ} (hBB' : B ⊆ B')
    (hPsupp : ∀ m k, m ≤ k → P m k = 0) (n z : ℕ) :
    enterBandKer P B n z
      = ∑ x ∈ B', enterBandKer P B' n x * enterBandKer P B x z := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h' : n ∈ B'
    · -- first hit is n: enterBandKer P B' n x = [x = n], sum collapses
      have hpt : ∀ x, enterBandKer P B' n x * enterBandKer P B x z
          = if x = n then enterBandKer P B n z else 0 := by
        intro x
        rw [enterBandKer_eq (P := P) (B := B') n x, if_pos h']
        by_cases hx : x = n
        · rw [if_pos hx, one_mul, hx, if_pos rfl]
        · rw [if_neg hx, zero_mul, if_neg hx]
      rw [Finset.sum_congr rfl (fun x _ => hpt x),
        Finset.sum_ite_eq' B' n (fun _ => enterBandKer P B n z), if_pos h']
    · -- n ∉ B', hence n ∉ B; one P-step + IH
      have hB : n ∉ B := fun hc => h' (hBB' hc)
      -- LHS expansion
      have hLHS : enterBandKer P B n z = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
        rw [enterBandKer_eq, if_neg hB]
      -- RHS: expand enterBandKer P B' n x, swap sums, apply IH per k
      have hRHS : (∑ x ∈ B', enterBandKer P B' n x * enterBandKer P B x z)
          = ∑ k ∈ Finset.range n,
              P n k * (∑ x ∈ B', enterBandKer P B' k x * enterBandKer P B x z) := by
        have hxexp : ∀ x, enterBandKer P B' n x * enterBandKer P B x z
            = ∑ k ∈ Finset.range n, P n k * enterBandKer P B' k x * enterBandKer P B x z := by
          intro x
          rw [enterBandKer_eq (P := P) (B := B') n x, if_neg h', Finset.sum_mul]
        rw [Finset.sum_congr rfl (fun x _ => hxexp x), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => by ring)
      rw [hRHS]
      rw [hLHS]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [ih k (Finset.mem_range.mp hk)]

/-- **L2 — factor entrance through the ceiling level.**  Let `C = R + A R`, `B = ceilBand R (A R)`
(`= {rnk < C}`), and `L = (ceilBand C 1).filter (C ≤ rnk ·)` (`= {rnk = C}`).  For any high start
`n` with `C ≤ rnk n`, the part of the first-entrance law into `B` that first passes through the
ceiling level `L` is bounded by the full first-entrance law:

  `∑_{x ∈ L} enterBandKer Pker (ceilBand C 1) n x · enterBandKer Pker B x z
      ≤ enterBandKer Pker B n z`.

(Overshoot landings — where the chain jumps from `rnk ≥ C` directly into `B = {rnk < C}` — are the
discarded nonnegative terms of the tower identity over `ceilBand C 1`.) -/
theorem enterBandKer_factor_through_ceiling_level (R : ℕ) (A : ℕ → ℕ) (n z : ℕ)
    (hn : R + A R ≤ rnk n) :
    ∑ x ∈ (ceilBand (R + A R) 1).filter (fun x => R + A R ≤ rnk x),
        enterBandKer Pker (ceilBand (R + A R) 1) n x
          * enterBandKer Pker (ceilBand R (A R)) x z
      ≤ enterBandKer Pker (ceilBand R (A R)) n z := by
  classical
  set C := R + A R with hC
  -- B = ceilBand R (A R) = {rnk < C}; B' = ceilBand C 1 = {rnk < C+1} = {rnk ≤ C}; B ⊆ B'
  have hBB' : ceilBand R (A R) ⊆ ceilBand C 1 := by
    intro x hx
    rw [mem_ceilBand_iff] at hx ⊢
    omega
  -- the tower identity over B' = ceilBand C 1
  have htower := enterBandKer_tower (P := Pker) (B := ceilBand R (A R)) (B' := ceilBand C 1)
    hBB' Pker_supp n z
  rw [htower]
  -- restrict the B'-sum to its level-C filter; discard nonnegative overshoot terms
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro x _ _
    exact mul_nonneg
      (enterBandKer_nonneg (fun a b => Pker_nonneg a b) n x)
      (enterBandKer_nonneg (fun a b => Pker_nonneg a b) x z)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# T2.1 (honest restatement): the rank-drop kernel and its exponential tail majorant

The pointwise rank-drop *local limit* `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y`-window whose edges oscillate with `frac(3√v)`).  The engine, however, does not consume that limit; it consumes a
one-sided pair:

* an **exponential tail majorant** of the rank-drop, uniform in `v` (this file, `Pker_rankDrop_tail_majorant`);
* a **phase-uniform per-drop minorization** `rankDropKer v 1, rankDropKer v 2 ≥ η` (the genuinely
  new analytic input; see the gap doc).

This file builds the tail majorant.  An *upper* bound on the rank-drop is unaffected by the floor
oscillation: a rank drop exceeding `A` forces a *large jump* `m ≳ (A/3)√v`, whose `erdosWeight`-mass
is exponentially small in `A` (banked block-majorant machinery `left_half_tail_sum_le_block_majorants`
for the bulk `2m ≤ v` half, and `right_half_kernel_sum_le` for the `2m > v` half).

`rankDropKer` is the rank-drop law of the predecessor kernel `Pker`; it is exactly the pushforward of
`Pker v ·` under the rank-drop `k ↦ rnk v - rnk k`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- `rankDropKer` is nonnegative. -/
lemma rankDropKer_nonneg (v d : ℕ) : 0 ≤ rankDropKer v d :=
  Finset.sum_nonneg (fun k _ => Pker_nonneg v k)

/-- The rank-drop tail `∑_{d > A} rankDropKer v d` regroups exactly as the `Pker`-mass over the set of
predecessors `k` whose rank-drop exceeds `A`. -/
lemma rankDropKer_tail_eq_mass (v A : ℕ) :
    (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
      = ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
          Pker v k := by
  classical
  unfold rankDropKer
  -- make both an honest double sum over range v × range v of guarded terms
  have hLHS : (∑ d ∈ (Finset.range v).filter (A < ·),
        ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k)
      = ∑ d ∈ Finset.range v, ∑ k ∈ Finset.range v,
          (if A < d then (if rnk v - rnk k = d then Pker v k else 0) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by rw [if_pos hAd])
    · rw [if_neg hAd, Finset.sum_eq_zero (fun k _ => by rw [if_neg hAd])]
  rw [hLHS, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- inner: ∑_{d ∈ range v} (if A < d then (if rnk v − rnk k = d then Pker v k else 0) else 0)
  by_cases hkv : A < rnk v - rnk k ∧ rnk v - rnk k < v
  · rw [if_pos hkv]
    rw [Finset.sum_eq_single (rnk v - rnk k)]
    · rw [if_pos hkv.1, if_pos rfl]
    · intro d _ hd
      by_cases hAd : A < d
      · rw [if_pos hAd, if_neg (by exact fun h => hd h.symm)]
      · rw [if_neg hAd]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hkv.2) hmem
  · rw [if_neg hkv]
    refine Finset.sum_eq_zero (fun d hd => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd]
      by_cases hdd : rnk v - rnk k = d
      · exact absurd ⟨hdd ▸ hAd, hdd ▸ Finset.mem_range.mp hd⟩ hkv
      · rw [if_neg hdd]
    · rw [if_neg hAd]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# T2.1 Step 1a: the phase-uniform per-drop minorization

The pointwise rank-drop local limit `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y = m/√v`-window whose edges SLIDE with `frac(3√v)`).
The engine, however, only needs a one-sided pair: the exp-tail majorant (banked in
`RankDropKer.lean`, `Pker_rankDrop_tail_majorant`) and a **phase-uniform per-drop minorization**

  `∃ η > 0, ∀ᶠ v, η ≤ rankDropKer v 1 ∧ η ≤ rankDropKer v 2`,

which is this file's `Pker_rankDrop_minorization`.

The minorization is TRUE but cannot use the banked per-`(a,b)` window limit `erdos_kernel_window`
directly: no *single* fixed `(a,b)` y-sub-window lies in the drop-1 set for all phases (the drop-1
windows over phases have empty intersection: `frac=0` gives `(0,2/3]`, `frac→1` gives `(2/3,4/3]`).

**Strategy (uniform-in-endpoints via a finite phase cover).**  A fixed y-sub-window `(a,b]` maps
entirely into the floor-induced drop-`d` set exactly when the phase `t = 3√v − ⌊3√v⌋` lies in the
open interval `(3b/2 − d, 3a/2 − d + 1)`.  Finitely many fixed sub-windows whose `t`-intervals cover
`[0,1)` therefore certify, for *every* phase, at least one sub-window entirely inside the drop-`d`
set; its window mass is bounded below by the banked positive limit `modelIntegral C a b`.  Taking
`η := min over the finite family of (modelIntegral C a b)/2 > 0` gives a phase-uniform bound.

The analytic heart is `drop_eq_of_window_mem`: every integer `m ∈ (a√v, b√v]`, under the phase
condition, has rank-drop exactly `d`.  This uses the sqrt-gap algebra of `window_rank_drop`
two-sidedly (`√v − √(v−m) = m/(√v+√(v−m))`, sandwiched by `m/(2√v)` and `m/(2√v−b)`).

Opus-authored.  Imports the banked bricks; does not modify them.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology BigOperators Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- **Sqrt-gap two-sided bound.**  For `1 ≤ m`, `m < v`, the sqrt gap `g = √v − √(v−m)` satisfies
`m/(2√v) ≤ g ≤ m/(2√v − √v·(m/v))`… we use the cleaner pair: `m/(2√v) ≤ g` and, when
`m ≤ b√v < 2v`, `g ≤ m/(2√v − b√v/√v·…)`.  Concretely: `g·(√v + √(v−m)) = m`, and
`√v − b ≤ √(v−m) ≤ √v`. -/
lemma sqrt_gap_bounds {v m : ℕ} (hm1 : 1 ≤ m) (hmv : m < v) :
    Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ)
        = (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ)) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hcast : ((v - m : ℕ) : ℝ) = (v : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hmv)]
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hsvm : 0 ≤ Real.sqrt ((v - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsumpos : 0 < Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by linarith
  have hprod : (Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ))
      * (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ)) = (m : ℝ) := by
    have e1 : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hvpos.le
    have e2 : Real.sqrt ((v - m : ℕ) : ℝ) ^ 2 = (v : ℝ) - (m : ℝ) := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  rw [eq_div_iff (ne_of_gt hsumpos)]
  exact hprod

/-- **Membership in the drop-`d` set.**  Fix `0 < a < b` and `d ≥ 1`.  Suppose `v` is large enough
that `√v ≥ b` (so `2√v − b ≥ √v > 0`) and the **phase conditions** hold:

* (A, lower) `(rnk v : ℝ) − d + 3b/2 + 3b²/(2√v) ≤ 3√v`,
* (B, upper) `3√v ≤ (rnk v : ℝ) − d + 1 + 3a/2`.

Then every integer `m` with `a√v < m ≤ b√v` has rank-drop exactly `d`: `rnk v − rnk (v−m) = d`. -/
lemma drop_eq_of_window_mem {a b : ℝ} (ha : 0 < a) (hab : a < b) {d v m : ℕ}
    (hd : 1 ≤ d) (hrnkd : d ≤ rnk v) (hsvb : b < Real.sqrt (v : ℝ))
    (hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) ≤ 3 * Real.sqrt (v : ℝ))
    (hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2)
    (hmlo : a * Real.sqrt (v : ℝ) < (m : ℝ)) (hmhi : (m : ℝ) ≤ b * Real.sqrt (v : ℝ)) :
    rnk v - rnk (v - m) = d := by
  have hsv : 0 < Real.sqrt (v : ℝ) := lt_trans (by linarith) hsvb
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    by_contra h
    push_neg at h
    have : (v : ℝ) = 0 := le_antisymm h (by positivity)
    rw [this, Real.sqrt_zero] at hsv; exact (lt_irrefl _ hsv)
  have hvN : 0 < v := by exact_mod_cast hvpos
  -- m ≥ 1 and m < v
  have hm1 : 1 ≤ m := by
    by_contra h
    push_neg at h
    interval_cases m
    · simp only [Nat.cast_zero] at hmlo
      nlinarith [hmlo, ha, hsv]
  have hmlt : m < v := by
    -- m ≤ b√v ≤ √v·√v = v, and strict since b<√v... use m ≤ b√v and b ≤ √v
    have hmv : (m : ℝ) ≤ b * Real.sqrt (v : ℝ) := hmhi
    have hbsv : b * Real.sqrt (v : ℝ) < Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) := by
      nlinarith [hsv, hsvb]
    have : (m : ℝ) < (v : ℝ) := by
      rw [Real.mul_self_sqrt hvpos.le] at hbsv; linarith
    exact_mod_cast this
  -- gap algebra
  have hsvm0 : 0 ≤ Real.sqrt ((v - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsvm_le : Real.sqrt ((v - m : ℕ) : ℝ) ≤ Real.sqrt (v : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le v m)
  have hgap := sqrt_gap_bounds hm1 hmlt
  set g : ℝ := Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ) with hgdef
  -- bound √(v−m) ≥ √v − b  (since g ≤ m/√v ≤ b)
  have hg_ub_simple : g ≤ b := by
    rw [hgap]
    -- m/(√v+√(v−m)) ≤ m/√v ≤ b
    have hden : Real.sqrt (v : ℝ) ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by linarith
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / Real.sqrt (v : ℝ) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hsv hden
    have h2 : (m : ℝ) / Real.sqrt (v : ℝ) ≤ b := by
      rw [div_le_iff₀ hsv]; linarith [hmhi]
    linarith [h1, h2]
  have hsvm_lb : Real.sqrt (v : ℝ) - b ≤ Real.sqrt ((v - m : ℕ) : ℝ) := by
    have : g ≤ b := hg_ub_simple
    rw [hgdef] at this; linarith
  -- UPPER side: 3√(v−m) < 3√v − 3a/2,  via g > a/2
  have hg_lb : (a : ℝ) / 2 < g := by
    rw [hgap]
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))]
    -- a/2·(√v+√(v−m)) ≤ a/2·(2√v) = a√v < m
    have : a / 2 * (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ a / 2 * (2 * Real.sqrt (v : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ a/2)
      linarith [hsvm_le]
    have ha2 : a / 2 * (2 * Real.sqrt (v : ℝ)) = a * Real.sqrt (v : ℝ) := by ring
    linarith [hmlo]
  have hupper : 3 * Real.sqrt ((v - m : ℕ) : ℝ) < 3 * Real.sqrt (v : ℝ) - 3 * a / 2 := by
    have : Real.sqrt ((v - m : ℕ) : ℝ) = Real.sqrt (v : ℝ) - g := by rw [hgdef]; ring
    rw [this]; linarith [hg_lb]
  -- LOWER side: 3√(v−m) ≥ 3√v − 3b/2 − 3b²/(2√v),  via g ≤ b√v/(2√v−b)
  have hg_ub : g ≤ 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2 := by
    -- g = m/(√v+√(v−m)) ≤ b√v/(2√v−b);  b√v/(2√v−b) − b/2 = b²/(2(2√v−b)) ≤ b²/(2√v)
    rw [hgap]
    have hden_lb : 2 * Real.sqrt (v : ℝ) - b ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by
      linarith [hsvm_lb]
    have hden_pos : 0 < 2 * Real.sqrt (v : ℝ) - b := by linarith [hsvb, hab, ha]
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hden_pos hden_lb
    have h2 : (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) ≤ b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      gcongr
    have h3 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
        ≤ 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2 := by
      -- RHS = b²/(2√v) + b/2;  LHS − b/2 = b²/(2(2√v−b)) ≤ b²/(2√v)
      have hrhs_eq : 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2
          = b ^ 2 / (2 * Real.sqrt (v : ℝ)) + b / 2 := by ring
      rw [hrhs_eq]
      have hstep1 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
          = b ^ 2 / (2 * (2 * Real.sqrt (v : ℝ) - b)) + b / 2 := by
        rw [div_add_div _ _ (by positivity : 2 * (2 * Real.sqrt (v:ℝ) - b) ≠ 0)
              (by norm_num : (2:ℝ) ≠ 0), div_eq_div_iff (by positivity) (by positivity)]
        ring
      rw [hstep1]
      have hmono : b ^ 2 / (2 * (2 * Real.sqrt (v : ℝ) - b)) ≤ b ^ 2 / (2 * Real.sqrt (v : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hsvb, hab, ha]
      linarith [hmono]
    linarith [h1, h2, h3]
  have hlower : 3 * Real.sqrt (v : ℝ) - 3 * b / 2 - 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
      ≤ 3 * Real.sqrt ((v - m : ℕ) : ℝ) := by
    have : Real.sqrt ((v - m : ℕ) : ℝ) = Real.sqrt (v : ℝ) - g := by rw [hgdef]; ring
    rw [this]; nlinarith [hg_ub]
  -- Now convert to rnk via floor and phase conditions
  -- rnk(v−m) = ⌊3√(v−m)⌋
  have hrnk_eq : rnk (v - m) = ⌊3 * Real.sqrt ((v - m : ℕ) : ℝ)⌋₊ := rfl
  -- L := rnk v; L ≤ 3√v < L+1
  obtain ⟨hLle, hLlt⟩ := rnk_sqrt_bounds v
  -- d ≤ rnk v (so rnk v - d is a sensible ℕ subtraction) : from phase A and B
  -- Upper bound on rnk(v−m): 3√(v−m) < L − d + 1  ⟹  rnk(v−m) ≤ L − d
  have hupper2 : 3 * Real.sqrt ((v - m : ℕ) : ℝ) < (rnk v : ℝ) - (d : ℝ) + 1 := by
    linarith [hupper, hB]
  have hlower2 : (rnk v : ℝ) - (d : ℝ) ≤ 3 * Real.sqrt ((v - m : ℕ) : ℝ) := by
    linarith [hlower, hA]
  -- need rnk v ≥ d
  have hdleN : d ≤ rnk v := hrnkd
  have hdle : (d : ℝ) ≤ (rnk v : ℝ) := by exact_mod_cast hdleN
  -- rnk(v−m) ≤ rnk v − d
  have hub_nat : rnk (v - m) ≤ rnk v - d := by
    rw [hrnk_eq]
    -- ⌊3√(v−m)⌋ < (rnk v − d) + 1 in ℕ, from 3√(v−m) < rnk v − d + 1 in ℝ
    have hfl : ⌊3 * Real.sqrt ((v - m : ℕ) : ℝ)⌋₊ < (rnk v - d) + 1 := by
      apply Nat.floor_lt' (by omega : (rnk v - d) + 1 ≠ 0) |>.mpr
      push_cast
      rw [Nat.cast_sub hdleN]
      linarith [hupper2]
    omega
  -- rnk(v−m) ≥ rnk v − d
  have hlb_nat : rnk v - d ≤ rnk (v - m) := by
    rw [hrnk_eq]
    apply Nat.le_floor
    push_cast
    have : ((rnk v - d : ℕ) : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) := by
      rw [Nat.cast_sub hdleN]
    linarith [hlower2, this]
  have : rnk (v - m) = rnk v - d := le_antisymm hub_nat hlb_nat
  omega

/-- **Window-mass minorization of one drop.**  Under the phase conditions of
`drop_eq_of_window_mem` (for a fixed `(a,b)` and drop `d`), the rank-drop mass at `d` is at least
the (reflected) window mass `kernelWindow a b v / kernelMass v`: every step into the y-window
`(a√v, b√v]` is a drop-`d` step. -/
lemma rankDropKer_ge_window {a b : ℝ} (ha : 0 < a) (hab : a < b) {d v : ℕ}
    (hd : 1 ≤ d) (hrnkd : d ≤ rnk v) (hsvb : b < Real.sqrt (v : ℝ))
    (hkpos : 0 < kernelMass v)
    (hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
        ≤ 3 * Real.sqrt (v : ℝ))
    (hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2) :
    kernelWindow a b v / kernelMass v ≤ rankDropKer v d := by
  classical
  have hsvpos : (0 : ℝ) < Real.sqrt (v : ℝ) := by linarith [hsvb, ha, hab]
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt (Nat.cast_nonneg v)
    nlinarith [hsvpos, hsq]
  have hvN : 0 < v := by exact_mod_cast hvpos
  -- reflect the window mass / kernelMass into the predecessor coordinate as a masked Pker-sum
  have hreflect : kernelWindow a b v / kernelMass v
      = ∑ k ∈ Finset.Icc 1 (v - 1),
          (if a * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ)
              ∧ ((v - k : ℕ) : ℝ) ≤ b * Real.sqrt (v : ℝ)
            then Pker v k else 0) := by
    rw [kernelWindow, ← sum_Icc_reflect_sub v
      (fun m => if a * Real.sqrt (v : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (v : ℝ)
        then erdosWeight v m else 0), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hw : a * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ)
        ∧ ((v - k : ℕ) : ℝ) ≤ b * Real.sqrt (v : ℝ)
    · rw [if_pos hw, if_pos hw]
      unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
    · rw [if_neg hw, if_neg hw, zero_div]
  rw [hreflect, ← Finset.sum_filter]
  unfold rankDropKer
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · -- the window-filter ⊆ the drop-d filter
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    -- m := v − k ∈ (a√v, b√v] ⟹ drop = d
    have hdrop := drop_eq_of_window_mem ha hab (d := d) (v := v) (m := v - k)
      hd hrnkd hsvb hA hB hw1 hw2
    rwa [Nat.sub_sub_self (by omega : k ≤ v)] at hdrop
  · intro k _ _; exact Pker_nonneg v k

/-- The integral of the positive Erdős density over a nondegenerate interval is positive. -/
lemma modelIntegral_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : 0 < Model.modelIntegral C a b := by
  have hC := C_pos
  rw [Model.modelIntegral]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
      have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
        continuous_const.mul continuous_id
      have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
      exact h1.mul h2
    exact hc.intervalIntegrable _ _
  · intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_le_of_lt ha hy.1
    have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
    have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
    nlinarith [mul_pos (mul_pos hπ hy0) he]
  · exact hab

/-- **Eventual window-mass-over-total lower bound** for a fixed nondegenerate `(a,b)`:
`kernelWindow a b v / kernelMass v ≥ modelIntegral C a b / 2 > 0` eventually in `v`. -/
lemma window_div_mass_ge_eventually {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ v : ℕ in atTop,
      Model.modelIntegral C a b / 2 ≤ kernelWindow a b v / kernelMass v := by
  have hIpos := modelIntegral_pos ha hab
  -- window mass → modelIntegral, so eventually ≥ (3/4)·I
  have hwin := Model.erdos_kernel_window (a := a) (b := b) ha hab
  have hwin_ge : ∀ᶠ v : ℕ in atTop,
      (3 / 4) * Model.modelIntegral C a b ≤ kernelWindow a b v := by
    have hev := (tendsto_order.1 hwin).1 ((3 / 4) * Model.modelIntegral C a b) (by nlinarith [hIpos])
    filter_upwards [hev] with v hv
    -- kernelWindow a b v is definitionally the masked sum
    exact hv.le
  -- kernelMass → 1, so eventually kernelMass ≤ 3/2 and ≥ 1/2 > 0
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hKsmall : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  filter_upwards [hwin_ge, hKev, hKsmall, eventually_ge_atTop 1] with v hwinv hKv hKsv hv1
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKv
  have hSge : (1 : ℝ) / 2 ≤ kernelMass v := by linarith [hKsv]
  have hSle : kernelMass v ≤ 3 / 2 := by linarith [hKsv]
  have hSpos : (0 : ℝ) < kernelMass v := by linarith
  -- I/2 ≤ (3/4)I / (3/2) ≤ kernelWindow / kernelMass
  rw [le_div_iff₀ hSpos]
  -- I/2 · kernelMass ≤ I/2 · (3/2) = (3/4)I ≤ kernelWindow
  calc Model.modelIntegral C a b / 2 * kernelMass v
      ≤ Model.modelIntegral C a b / 2 * (3 / 2) := by
        apply mul_le_mul_of_nonneg_left hSle (by linarith [hIpos])
    _ = (3 / 4) * Model.modelIntegral C a b := by ring
    _ ≤ kernelWindow a b v := hwinv

/-- **Subwindow drop bound, in `t`-band form.**  Fix `0 < a < b`, drop `d ≥ 1`, and rational
`t`-band endpoints `tlo ≤ thi` with strict margins
`3b/2 − d < tlo` and `thi < 3a/2 − d + 1`.  Then eventually in `v`: whenever the phase
`t := 3√v − rnk v` lies in `[tlo, thi]`, the rank-drop mass at `d` is `≥ modelIntegral C a b / 2`. -/
lemma rankDropKer_ge_const_of_tband {a b tlo thi : ℝ} (ha : 0 < a) (hab : a < b)
    {d : ℕ} (hd : 1 ≤ d) (htle : tlo ≤ thi)
    (hmA : 3 * b / 2 - (d : ℝ) < tlo) (hmB : thi < 3 * a / 2 - (d : ℝ) + 1) :
    ∀ᶠ v : ℕ in atTop,
      (tlo ≤ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ)
        ∧ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) ≤ thi) →
      Model.modelIntegral C a b / 2 ≤ rankDropKer v d := by
  have hIge := window_div_mass_ge_eventually (a := a) (b := b) ha.le hab
  -- error term ε_v = 3b²/(2√v) → 0; need ε_v < tlo − (3b/2 − d)
  set εmar : ℝ := tlo - (3 * b / 2 - (d : ℝ)) with hεdef
  have hεpos : 0 < εmar := by rw [hεdef]; linarith [hmA]
  have herr : ∀ᶠ v : ℕ in atTop, 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) ≤ εmar := by
    have htend : Tendsto (fun v : ℕ => 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_le_const hεpos
  -- need √v > b and rnk v ≥ d eventually
  have hsvb : ∀ᶠ v : ℕ in atTop, b < Real.sqrt (v : ℝ) := by
    have htend : Tendsto (fun v : ℕ => Real.sqrt (v : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_gt_atTop b
  have hrnkd : ∀ᶠ v : ℕ in atTop, d ≤ rnk v := by
    -- rnk v = ⌊3√v⌋ ≥ d as soon as 3√v ≥ d
    have hsq : Tendsto (fun v : ℕ => 3 * Real.sqrt (v : ℝ)) atTop atTop := by
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 3)
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsq.eventually_ge_atTop ((d : ℝ))] with v hv
    show d ≤ ⌊3 * Real.sqrt (v : ℝ)⌋₊
    exact Nat.le_floor (by push_cast; linarith [hv])
  have hkpos : ∀ᶠ v : ℕ in atTop, 0 < kernelMass v := by
    obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
    have hKsmall : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
      have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
      exact htend.eventually_le_const (by norm_num)
    filter_upwards [hKev, hKsmall] with v hKv hKsv
    obtain ⟨hSlo, _⟩ := abs_le.1 hKv
    linarith [hKsv]
  filter_upwards [hIge, herr, hsvb, hrnkd, hkpos] with v hIgev herrv hsvbv hrnkdv hkposv
  intro ⟨htlo, hthi⟩
  -- derive phase conditions A, B from t-band + margins
  have hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
      ≤ 3 * Real.sqrt (v : ℝ) := by
    -- 3√v − rnk v ≥ tlo ≥ 3b/2 − d + ε_v
    have : tlo ≥ 3 * b / 2 - (d : ℝ) + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) := by
      rw [hεdef] at *; linarith [herrv]
    linarith [htlo, this]
  have hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2 := by
    -- 3√v − rnk v ≤ thi < 3a/2 − d + 1
    linarith [hthi, hmB]
  exact le_trans hIgev (rankDropKer_ge_window ha hab hd hrnkdv hsvbv hkposv hA hB)

/-! ### The eight subwindows of the finite phase cover

For drop `d = 1` (four windows) and drop `d = 2` (four windows), each with rational endpoints whose
`t`-band `[3b/2−d, 3a/2−d+1]` covers a piece of `[0,1)`; the eight `t`-bands together cover `[0,1)`
twice (once for each drop), as verified numerically.  We package each subwindow's `t`-band drop
bound and take `η` to be the minimum of the eight `modelIntegral/2` values. -/

/-- **T2.1 Step 1a — phase-uniform per-drop minorization.**  There is `η > 0` such that, eventually
in `v`, both `rankDropKer v 1 ≥ η` and `rankDropKer v 2 ≥ η`.  The drop-`d` `m`-window slides with
`frac(3√v)`, so no single fixed sub-window certifies the mass; instead a finite family of fixed
sub-windows whose phase `t`-bands cover `[0,1)` (separately for `d = 1` and `d = 2`) is used, and
`η` is the minimum of their (positive) window half-masses. -/
theorem Pker_rankDrop_minorization :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ v : ℕ in atTop,
      η ≤ rankDropKer v 1 ∧ η ≤ rankDropKer v 2 := by
  -- the eight half-integrals
  set I1 := Model.modelIntegral C 0.10 0.40 / 2 with hI1
  set I2 := Model.modelIntegral C 0.40 0.66 / 2 with hI2
  set I3 := Model.modelIntegral C 0.62 0.90 / 2 with hI3
  set I4 := Model.modelIntegral C 0.86 1.14 / 2 with hI4
  set J1 := Model.modelIntegral C 0.72 1.00 / 2 with hJ1
  set J2 := Model.modelIntegral C 0.96 1.24 / 2 with hJ2
  set J3 := Model.modelIntegral C 1.20 1.48 / 2 with hJ3
  set J4 := Model.modelIntegral C 1.44 1.74 / 2 with hJ4
  -- positivity of each
  have pI1 : 0 < I1 := by rw [hI1]; have := modelIntegral_pos (a := 0.10) (b := 0.40) (by norm_num) (by norm_num); linarith
  have pI2 : 0 < I2 := by rw [hI2]; have := modelIntegral_pos (a := 0.40) (b := 0.66) (by norm_num) (by norm_num); linarith
  have pI3 : 0 < I3 := by rw [hI3]; have := modelIntegral_pos (a := 0.62) (b := 0.90) (by norm_num) (by norm_num); linarith
  have pI4 : 0 < I4 := by rw [hI4]; have := modelIntegral_pos (a := 0.86) (b := 1.14) (by norm_num) (by norm_num); linarith
  have pJ1 : 0 < J1 := by rw [hJ1]; have := modelIntegral_pos (a := 0.72) (b := 1.00) (by norm_num) (by norm_num); linarith
  have pJ2 : 0 < J2 := by rw [hJ2]; have := modelIntegral_pos (a := 0.96) (b := 1.24) (by norm_num) (by norm_num); linarith
  have pJ3 : 0 < J3 := by rw [hJ3]; have := modelIntegral_pos (a := 1.20) (b := 1.48) (by norm_num) (by norm_num); linarith
  have pJ4 : 0 < J4 := by rw [hJ4]; have := modelIntegral_pos (a := 1.44) (b := 1.74) (by norm_num) (by norm_num); linarith
  -- η := min of the eight
  set η : ℝ := min (min (min I1 I2) (min I3 I4)) (min (min J1 J2) (min J3 J4)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (lt_min pI1 pI2) (lt_min pI3 pI4))
      (lt_min (lt_min pJ1 pJ2) (lt_min pJ3 pJ4))
  -- the eight t-band drop bounds
  have b1 := rankDropKer_ge_const_of_tband (a := 0.10) (b := 0.40) (tlo := 0) (thi := 0.1)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2 := rankDropKer_ge_const_of_tband (a := 0.40) (b := 0.66) (tlo := 0.1) (thi := 0.5)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rankDropKer_ge_const_of_tband (a := 0.62) (b := 0.90) (tlo := 0.5) (thi := 0.85)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b4 := rankDropKer_ge_const_of_tband (a := 0.86) (b := 1.14) (tlo := 0.85) (thi := 1)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c1 := rankDropKer_ge_const_of_tband (a := 0.72) (b := 1.00) (tlo := 0) (thi := 0.05)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 := rankDropKer_ge_const_of_tband (a := 0.96) (b := 1.24) (tlo := 0.05) (thi := 0.4)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c3 := rankDropKer_ge_const_of_tband (a := 1.20) (b := 1.48) (tlo := 0.4) (thi := 0.75)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c4 := rankDropKer_ge_const_of_tband (a := 1.44) (b := 1.74) (tlo := 0.75) (thi := 1)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- t ∈ [0,1) always
  have hphase : ∀ᶠ v : ℕ in atTop,
      0 ≤ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) ∧ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) < 1 := by
    filter_upwards with v
    obtain ⟨h1, h2⟩ := rnk_sqrt_bounds v
    exact ⟨by linarith, by linarith⟩
  refine ⟨η, hηpos, ?_⟩
  filter_upwards [b1, b2, b3, b4, c1, c2, c3, c4, hphase]
    with v hb1 hb2 hb3 hb4 hc1 hc2 hc3 hc4 ⟨ht0, ht1⟩
  set t : ℝ := 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) with htdef
  -- η ≤ each I/J value
  have leI1 : η ≤ I1 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have leI2 : η ≤ I2 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have leI3 : η ≤ I3 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have leI4 : η ≤ I4 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have leJ1 : η ≤ J1 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have leJ2 : η ≤ J2 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have leJ3 : η ≤ J3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have leJ4 : η ≤ J4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  constructor
  · -- drop 1: pick subwindow by where t lies
    rcases le_or_gt t 0.1 with h | h
    · exact le_trans leI1 (hb1 ⟨ht0, h⟩)
    · rcases le_or_gt t 0.5 with h2 | h2
      · exact le_trans leI2 (hb2 ⟨le_of_lt h, h2⟩)
      · rcases le_or_gt t 0.85 with h3 | h3
        · exact le_trans leI3 (hb3 ⟨le_of_lt h2, h3⟩)
        · exact le_trans leI4 (hb4 ⟨le_of_lt h3, le_of_lt ht1⟩)
  · -- drop 2
    rcases le_or_gt t 0.05 with h | h
    · exact le_trans leJ1 (hc1 ⟨ht0, h⟩)
    · rcases le_or_gt t 0.4 with h2 | h2
      · exact le_trans leJ2 (hc2 ⟨le_of_lt h, h2⟩)
      · rcases le_or_gt t 0.75 with h3 | h3
        · exact le_trans leJ3 (hc3 ⟨le_of_lt h2, h3⟩)
        · exact le_trans leJ4 (hc4 ⟨le_of_lt h3, le_of_lt ht1⟩)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK T2-ceiling, L3: the rank-only ceiling-level hit lower bound

L3 (R7 route): the first-entrance law into the down-set `ceilBand C 1 = {rnk ≤ C}` from a high start
`n` (`rnk n ≥ C`) lands at the **exact ceiling level** `{rnk = C}` (vs overshooting to `{rnk < C}`)
with mass `≥ α`, *uniformly over all heights* `rnk n ≥ C`.

This is the rank-renewal mass lower bound.  It is NOT the naive `η^gap` (which decays with the
height): holding (drop-0 mass `rankDropKer v 0 = Θ(1)`) is folded out **inline** by a strong
induction on the value `v`, and the per-level overshoot tail is absorbed by a **subsolution**
`β : ℕ → ℝ`, antitone, `β 0 ≤ 1`, `β r ≥ α > 0`, satisfying the slope condition
`η · (β (r-1) − β r) ≥ ε_r · β r`, where `η` is the banked per-drop minorizer
(`Pker_rankDrop_minorization`) and `ε_r` the banked exponential overshoot tail
(`Pker_rankDrop_tail_majorant`).

The decomposition is
`g C v ≥ ∑_{d=0}^{r} rankDropKer v d · β(r−d)`  (`r = rnk v − C`),
and the slope condition forces `g C v ≥ β r ≥ α` by strong induction.

This file proves the two reusable cores:

* `pushforward_rankDrop`: `∑_{k<v} Pker v k · f (rnk v − rnk k) = ∑_{d ≤ rnk v} rankDropKer v d · f d`
  for any `f` (the rank-drop pushforward of one `Pker` step);
* `ceilingHit_ge_of_subsolution`: the abstract subsolution ⟹ uniform lower bound (strong induction).

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Exact ceiling-level hit mass.**  `ceilHit C v` is the first-entrance mass into the down-set
`ceilBand C 1 = {rnk ≤ C}` that lands at the exact ceiling level `{rnk = C}`. -/
noncomputable def ceilHit (C v : ℕ) : ℝ :=
  ∑ x ∈ (ceilBand C 1).filter (fun x => C ≤ rnk x), enterBandKer Pker (ceilBand C 1) v x

lemma ceilHit_nonneg (C v : ℕ) : 0 ≤ ceilHit C v :=
  Finset.sum_nonneg (fun x _ => enterBandKer_nonneg (fun a b => Pker_nonneg a b) v x)

/-- For a state already at the ceiling level (`rnk v = C`), the entrance is the point mass and the
exact-level hit mass is `1`. -/
lemma ceilHit_of_rnk_eq {C v : ℕ} (hv : rnk v = C) : ceilHit C v = 1 := by
  classical
  have hmem : v ∈ ceilBand C 1 := mem_ceilBand_iff.mpr (by omega)
  unfold ceilHit
  have hpt : ∀ x, enterBandKer Pker (ceilBand C 1) v x = if x = v then 1 else 0 := by
    intro x; rw [enterBandKer_eq, if_pos hmem]
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  rw [Finset.sum_ite_eq' ((ceilBand C 1).filter (fun x => C ≤ rnk x)) v (fun _ => (1:ℝ))]
  rw [if_pos (Finset.mem_filter.mpr ⟨hmem, by omega⟩)]

/-- **Rank-drop pushforward of one step.**  For any `f : ℕ → ℝ`, summing `Pker v k · f (rnk v − rnk k)`
over predecessors `k < v` equals `∑_{d ∈ range (rnk v + 1)} rankDropKer v d · f d`.  (Every
predecessor `k < v` has `rnk k ≤ rnk v`, so the drop `rnk v − rnk k` lies in `[0, rnk v]`.) -/
lemma pushforward_rankDrop (v : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range v, Pker v k * f (rnk v - rnk k))
      = ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d * f d := by
  classical
  -- group predecessors by their drop value
  have hgroup : (∑ k ∈ Finset.range v, Pker v k * f (rnk v - rnk k))
      = ∑ d ∈ Finset.range (rnk v + 1),
          ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k * f (rnk v - rnk k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => rnk v - rnk k)
        (t := Finset.range (rnk v + 1))]
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    have : rnk k ≤ rnk v := rnk_mono (le_of_lt hk)
    omega
  rw [hgroup]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  -- on the fiber, rnk v − rnk k = d, so f (rnk v − rnk k) = f d; factor out
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [(Finset.mem_filter.mp hk).2])]
  rw [← Finset.sum_mul]
  rfl

/-- **Ceiling-hit one-step recursion.**  For a high state `v` above the ceiling level
(`C < rnk v`), the exact-level hit mass satisfies the linear recursion
`ceilHit C v = ∑_{k<v} Pker v k · ceilHit C k`.  (One `Pker` step then the first-entrance kernel from
each predecessor; the level filter commutes with the linear expansion.) -/
lemma ceilHit_recursion {C v : ℕ} (hv : C < rnk v) :
    ceilHit C v = ∑ k ∈ Finset.range v, Pker v k * ceilHit C k := by
  classical
  have hnotmem : v ∉ ceilBand C 1 := by
    rw [mem_ceilBand_iff]; omega
  unfold ceilHit
  -- expand each entrance, swap sums
  have hexp : ∀ x, enterBandKer Pker (ceilBand C 1) v x
      = ∑ k ∈ Finset.range v, Pker v k * enterBandKer Pker (ceilBand C 1) k x := by
    intro x; rw [enterBandKer_eq, if_neg hnotmem]
  rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]

/-- **Inductive expansion bound.**  Assume a rank-indexed lower bound `β` (extended by `0` below the
ceiling) is available at every predecessor.  Then for `C < rnk v` the exact-level hit mass is at
least the rank-drop pushforward of `β`:
`ceilHit C v ≥ ∑_{d ≤ rnk v} rankDropKer v d · βbar (rnk v − d)`, where `βbar r := if C ≤ r then
β (r − C) else 0`. -/
lemma ceilHit_ge_pushforward {C v : ℕ} (β : ℕ → ℝ) (hv : C < rnk v)
    (hβ0 : ∀ r, 0 ≤ β r)
    (hIH : ∀ k, k < v → (if C ≤ rnk k then β (rnk k - C) else (0:ℝ)) ≤ ceilHit C k) :
    (∑ d ∈ Finset.range (rnk v + 1),
        rankDropKer v d * (if C ≤ rnk v - d then β (rnk v - d - C) else 0))
      ≤ ceilHit C v := by
  classical
  rw [ceilHit_recursion hv]
  rw [← pushforward_rankDrop v (fun d => if C ≤ rnk v - d then β (rnk v - d - C) else 0)]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hkv : k < v := Finset.mem_range.mp hk
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  -- rnk v − (rnk v − rnk k) = rnk k
  have hsub : rnk v - (rnk v - rnk k) = rnk k := by omega
  rw [hsub]
  exact mul_le_mul_of_nonneg_left (hIH k hkv) (Pker_nonneg v k)

/-- **Closing inequality from the subsolution slope.**  Fix `r ≥ 1` and a state `v` with
`rnk v = C + r`.  If the rank-drop law from `v` is a sub-probability (`∑_{d ≤ rnk v} rankDropKer v d
≤ 1`), satisfies the drop-1 minorization `rankDropKer v 1 ≥ η`, has overshoot tail
`∑_{r < d ≤ rnk v} rankDropKer v d ≤ ε r`, and `β` is antitone with the slope condition
`η · (β (r-1) − β r) ≥ ε r · β r`, then the pushforward dominates `β r`. -/
lemma pushforward_ge_beta {C v : ℕ} {η : ℝ} (β ε : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hrv : rnk v = C + r) (hC1 : 1 ≤ C) (hη0 : 0 ≤ η)
    (hβanti : Antitone β) (hβ0 : ∀ s, 0 ≤ β s)
    (htot : 1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
    (hmin1 : η ≤ rankDropKer v 1)
    (htail : ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => r < d), rankDropKer v d ≤ ε r)
    (hslope : ε r * β r ≤ η * (β (r-1) - β r)) :
    β r ≤ ∑ d ∈ Finset.range (rnk v + 1),
        rankDropKer v d * (if C ≤ rnk v - d then β (rnk v - d - C) else 0) := by
  classical
  -- abbreviate the summand's β-part as βr (r - d) for d ≤ r and 0 beyond
  set f : ℕ → ℝ := fun d => if C ≤ rnk v - d then β (rnk v - d - C) else 0 with hf
  -- on d ≤ r: f d = β (r - d); on d > r: f d = 0
  have hf_le : ∀ d, d ≤ r → f d = β (r - d) := by
    intro d hd; simp only [hf, hrv]
    rw [if_pos (by omega)]; congr 1; omega
  have hf_gt : ∀ d, r < d → f d = 0 := by
    intro d hd; simp only [hf, hrv]; rw [if_neg (show ¬ C ≤ C + r - d by omega)]
  -- f d ≥ β r for d ≤ r (β antitone), and f d = 0 ≥ 0 for d > r
  have hf_ge_βr : ∀ d, d ∈ Finset.range (rnk v + 1) → β r ≤ f d ∨ r < d := by
    intro d _; rcases le_or_gt d r with hd | hd
    · left; rw [hf_le d hd]; exact hβanti (by omega)
    · right; exact hd
  -- split the pushforward sum into d ≤ r (good) and d > r (overshoot, = 0)
  have hsplit : (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d * f d)
      = ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d), rankDropKer v d * f d := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (rnk v + 1)) (fun d => ¬ r < d)]
    have hzero : (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => ¬¬ r < d),
        rankDropKer v d * f d) = 0 := by
      refine Finset.sum_eq_zero (fun d hd => ?_)
      have : r < d := by have := (Finset.mem_filter.mp hd).2; omega
      rw [hf_gt d this, mul_zero]
    rw [hzero, add_zero]
  rw [hsplit]
  -- the good sum (d ≤ r): ∑ rankDropKer v d · β(r-d)
  set G := (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d) with hG
  have hGval : ∀ d ∈ G, rankDropKer v d * f d = rankDropKer v d * β (r - d) := by
    intro d hd
    have hdr : d ≤ r := by have := (Finset.mem_filter.mp hd).2; omega
    rw [hf_le d hdr]
  rw [Finset.sum_congr rfl hGval]
  -- decompose ∑_{d∈G} p_d β(r-d) = β r · (∑_{d∈G} p_d) + ∑_{d∈G} p_d (β(r-d) - β r)
  have hdecomp : (∑ d ∈ G, rankDropKer v d * β (r - d))
      = β r * (∑ d ∈ G, rankDropKer v d)
        + ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => by ring)
  rw [hdecomp]
  -- ∑_{d∈G} p_d = total − overshoot ≥ 1 − ε r? we only need ≥ 1 − tail. Use total ≤ 1 lower side:
  -- ∑_{d∈G} p_d = total − ∑_{d∉G} p_d, and ∑_{d∉G} p_d = overshoot ≤ ε r.
  have hGmass : (∑ d ∈ G, rankDropKer v d)
      = (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
        - ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => r < d), rankDropKer v d := by
    rw [hG]
    have := Finset.sum_filter_add_sum_filter_not (Finset.range (rnk v + 1)) (fun d => r < d)
      (rankDropKer v)
    -- filter (¬ r < d) is the complement of filter (r < d)
    have hcomm : (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d) =
        (Finset.range (rnk v + 1)).filter (fun d => ¬ (r < d)) := rfl
    linarith [this]
  -- excess ≥ η (β(r-1) - β r): keep only d=1 term, drop others (nonneg)
  have h1mem : (1 : ℕ) ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]; refine ⟨by omega, by omega⟩
  have hexcess_nn : ∀ d ∈ G, 0 ≤ rankDropKer v d * (β (r - d) - β r) := by
    intro d hd
    have hdr : d ≤ r := by have := (Finset.mem_filter.mp hd).2; omega
    exact mul_nonneg (rankDropKer_nonneg v d) (by linarith [hβanti (show r - d ≤ r by omega)])
  have hexcess : η * (β (r-1) - β r) ≤ ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
    have hsingle : rankDropKer v 1 * (β (r - 1) - β r)
        ≤ ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) :=
      Finset.single_le_sum hexcess_nn h1mem
    refine le_trans ?_ hsingle
    have hslope_nn : 0 ≤ β (r - 1) - β r := by linarith [hβanti (show r - 1 ≤ r by omega)]
    exact mul_le_mul_of_nonneg_right hmin1 hslope_nn
  -- combine
  have hmass_lb : (1 : ℝ) - ε r ≤ ∑ d ∈ G, rankDropKer v d := by
    rw [hGmass]; linarith [htot, htail]
  -- β r ≤ β r (1 − ε r) + ε r β r ≤ β r · mass + excess
  have hβr_nn : 0 ≤ β r := hβ0 r
  calc β r = β r * (1 - ε r) + ε r * β r := by ring
    _ ≤ β r * (∑ d ∈ G, rankDropKer v d) + η * (β (r-1) - β r) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hmass_lb hβr_nn
        · linarith [hslope]
    _ ≤ β r * (∑ d ∈ G, rankDropKer v d) + ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
        linarith [hexcess]

/-- **Abstract subsolution comparison (strong induction).**  Suppose `β` is antitone, nonnegative,
with `β 0 ≤ 1` and the slope condition `ε r · β r ≤ η · (β (r-1) − β r)` for all `r ≥ 1`.  Suppose
moreover that at every state `v` with `C < rnk v` the rank-drop law is a (sub)probability summing to
`≥ 1`, has drop-1 mass `≥ η`, and overshoot tail `≤ ε (rnk v − C)`.  Then `β (rnk v − C) ≤ ceilHit C v`
for every `v` with `C ≤ rnk v`. -/
lemma ceilHit_ge_beta {C : ℕ} {η : ℝ} (β ε : ℕ → ℝ) (hC1 : 1 ≤ C) (hη0 : 0 ≤ η)
    (hβanti : Antitone β) (hβ0 : ∀ s, 0 ≤ β s) (hβ01 : β 0 ≤ 1)
    (hslope : ∀ r, 1 ≤ r → ε r * β r ≤ η * (β (r-1) - β r))
    (hfacts : ∀ v, C < rnk v →
        (1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
        ∧ η ≤ rankDropKer v 1
        ∧ (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => rnk v - C < d), rankDropKer v d
              ≤ ε (rnk v - C))) :
    ∀ v, C ≤ rnk v → β (rnk v - C) ≤ ceilHit C v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hCv
    rcases eq_or_lt_of_le hCv with heq | hlt
    · -- rnk v = C: ceilHit = 1, β (0) ≤ 1
      rw [← heq, Nat.sub_self]
      rw [ceilHit_of_rnk_eq heq.symm]
      exact hβ01
    · -- C < rnk v
      set r := rnk v - C with hr
      have hr1 : 1 ≤ r := by omega
      have hrv : rnk v = C + r := by omega
      obtain ⟨htot, hmin1, htail⟩ := hfacts v hlt
      -- the inductive hypotheses at predecessors, packaged for ceilHit_ge_pushforward
      have hIH : ∀ k, k < v →
          (if C ≤ rnk k then β (rnk k - C) else (0:ℝ)) ≤ ceilHit C k := by
        intro k hkv
        by_cases hCk : C ≤ rnk k
        · rw [if_pos hCk]; exact ih k hkv hCk
        · rw [if_neg hCk]; exact ceilHit_nonneg C k
      have hpush := ceilHit_ge_pushforward (C := C) (v := v) β hlt hβ0 hIH
      have hbeta := pushforward_ge_beta (C := C) (v := v) (η := η) β ε hr1 hrv hC1 hη0
        hβanti hβ0 htot hmin1 htail (hslope r hr1)
      exact le_trans hbeta hpush

/-! ### The product subsolution `β`

`β r := (∏_{j=1}^{r} (1 + ε j / η))⁻¹`.  Antitone (`≥ 1` factors), `β 0 = 1`, slope condition is an
*equality* `η (β (r-1) − β r) = ε r · β r`, and the uniform lower bound
`β r ≥ exp(−(∑' ε)/η) > 0` via `1 + x ≤ exp x` and `∏ exp = exp ∑`. -/

/-- The product subsolution. -/
noncomputable def betaSub (ε : ℕ → ℝ) (η : ℝ) (r : ℕ) : ℝ :=
  (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))⁻¹

lemma betaSub_factor_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (j : ℕ) :
    0 < 1 + ε j / η := by
  have : 0 ≤ ε j / η := div_nonneg (hε j) hη.le
  linarith

lemma betaSub_prod_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (r : ℕ) :
    0 < ∏ j ∈ Finset.Icc 1 r, (1 + ε j / η) :=
  Finset.prod_pos (fun j _ => betaSub_factor_pos hη hε j)

lemma betaSub_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (r : ℕ) :
    0 < betaSub ε η r := by
  rw [betaSub]; exact inv_pos.mpr (betaSub_prod_pos hη hε r)

lemma betaSub_zero {ε : ℕ → ℝ} {η : ℝ} : betaSub ε η 0 = 1 := by
  rw [betaSub]; simp

/-- `β` is antitone: each extra factor `≥ 1` shrinks the inverse. -/
lemma betaSub_antitone {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) :
    Antitone (betaSub ε η) := by
  apply antitone_nat_of_succ_le
  intro r
  rw [betaSub, betaSub]
  apply inv_anti₀ (betaSub_prod_pos hη hε r)
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
  have hfac : 1 ≤ 1 + ε (r+1) / η := by
    have : 0 ≤ ε (r+1) / η := div_nonneg (hε (r+1)) hη.le; linarith
  nlinarith [betaSub_prod_pos hη hε r, hfac]

/-- The slope identity: `η · (β (r-1) − β r) = ε r · β r` for `r ≥ 1`. -/
lemma betaSub_slope {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) {r : ℕ} (hr : 1 ≤ r) :
    ε r * betaSub ε η r = η * (betaSub ε η (r-1) - betaSub ε η r) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the defining ratio β(s+1) = β(s) / F, with F = 1 + ε(s+1)/η
  have hps : 0 < ∏ j ∈ Finset.Icc 1 s, (1 + ε j / η) := betaSub_prod_pos hη hε s
  have hfac : 0 < 1 + ε (s+1) / η := betaSub_factor_pos hη hε (s+1)
  set P := ∏ j ∈ Finset.Icc 1 s, (1 + ε j / η) with hP
  have hβs : betaSub ε η s = P⁻¹ := rfl
  have hβs1 : betaSub ε η (s+1) = P⁻¹ * (1 + ε (s+1)/η)⁻¹ := by
    rw [betaSub, Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1), ← hP, mul_inv]
  rw [hβs, hβs1]
  have hPne : P ≠ 0 := ne_of_gt hps
  have hFne : (1 + ε (s+1)/η) ≠ 0 := ne_of_gt hfac
  have hηne : η ≠ 0 := ne_of_gt hη
  have hsum_ne : ε (1 + s) + η ≠ 0 := by
    have := hε (1 + s); positivity
  have hsum_ne' : η + ε (s + 1) ≠ 0 := by
    have := hε (s+1); positivity
  field_simp
  ring

/-- **Uniform lower bound** `β r ≥ exp(−S/η)` where `S = ∑' ε`.  Via `1 + x ≤ exp x`,
`∏ exp = exp ∑`, and partial-sum `≤ tsum` for the nonnegative summable `ε`. -/
lemma betaSub_ge {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j)
    (hsum : Summable ε) (r : ℕ) :
    Real.exp (-(∑' j, ε j) / η) ≤ betaSub ε η r := by
  rw [betaSub]
  have hprod_le : (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))
      ≤ Real.exp ((∑' j, ε j) / η) := by
    calc (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))
        ≤ ∏ j ∈ Finset.Icc 1 r, Real.exp (ε j / η) := by
          refine Finset.prod_le_prod (fun j _ => (betaSub_factor_pos hη hε j).le) ?_
          intro j _
          have := Real.add_one_le_exp (ε j / η); linarith
      _ = Real.exp (∑ j ∈ Finset.Icc 1 r, ε j / η) := by rw [Real.exp_sum]
      _ ≤ Real.exp ((∑' j, ε j) / η) := by
          apply Real.exp_le_exp.mpr
          rw [← Finset.sum_div]
          have hle : (∑ j ∈ Finset.Icc 1 r, ε j) ≤ ∑' j, ε j :=
            hsum.sum_le_tsum (Finset.Icc 1 r) (fun j _ => hε j)
          gcongr
  have hppos : 0 < ∏ j ∈ Finset.Icc 1 r, (1 + ε j / η) := betaSub_prod_pos hη hε r
  rw [neg_div, Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hppos]
  exact hprod_le

/-- `rankDropKer v d = 0` for `d > rnk v` (no predecessor can drop the rank by more than `rnk v`). -/
lemma rankDropKer_eq_zero_of_gt {v d : ℕ} (hd : rnk v < d) : rankDropKer v d = 0 := by
  unfold rankDropKer
  refine Finset.sum_eq_zero (fun k hk => ?_)
  exfalso
  have hkv : k < v := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have : rnk v - rnk k = d := (Finset.mem_filter.mp hk).2
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  omega

/-- Total rank-drop mass equals the row sum of `Pker`, hence `= 1` for `2 ≤ v`, `kernelMass v ≠ 0`. -/
lemma rankDropKer_total {v : ℕ} (hv : 2 ≤ v) (hS : kernelMass v ≠ 0) :
    (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d) = 1 := by
  have h := pushforward_rankDrop v (fun _ => (1:ℝ))
  simp only [mul_one] at h
  rw [← h, ← Pker_mass hv hS]

/-- `rnk v < v` once `10 ≤ v` (`3√v < v ⟺ v > 9`). -/
lemma rnk_lt_self {v : ℕ} (hv : 10 ≤ v) : rnk v < v := by
  have hvR : (10 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hsqlt : 3 * Real.sqrt (v : ℝ) < (v : ℝ) := by
    have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt (by positivity)
    have hspos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by linarith)
    -- 3√v < v ⟺ 3 < √v (÷√v) ⟸ √v > 3 ⟸ v > 9
    have hs3 : 3 < Real.sqrt (v : ℝ) := by
      have : (3:ℝ)^2 < Real.sqrt (v:ℝ)^2 := by rw [hsq]; nlinarith
      nlinarith [hspos, this]
    nlinarith [hs3, hspos, hsq]
  have : (rnk v : ℝ) < (v : ℝ) := lt_of_le_of_lt (rnk_sqrt_bounds v).1 hsqlt
  exact_mod_cast this

/-- **L3 — rank-only ceiling-level hit lower bound.**  There is `α > 0` so that, eventually in the
ceiling floor `C`, every start `n` of rank `≥ C` hits the exact ceiling level `{rnk = C}` (rather than
overshooting below) with first-entrance mass `≥ α`, uniformly over all heights. -/
theorem Pker_hit_ceiling_level_mass_lower :
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ C in atTop, ∀ n, C ≤ rnk n →
        α ≤ ∑ x ∈ (ceilBand C 1).filter (fun x => C ≤ rnk x),
              enterBandKer Pker (ceilBand C 1) n x := by
  classical
  -- the banked minorizer η and tail majorant ε
  obtain ⟨η, hηpos, hηev⟩ := Pker_rankDrop_minorization
  obtain ⟨γ, C₀, hγpos, htailev⟩ := Pker_rankDrop_tail_majorant
  -- ε A := C₀ (A+1) e^{−γ A}; summable, nonneg
  set ε : ℕ → ℝ := fun A => C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ)) with hεdef
  have hC₀nn : 0 ≤ C₀ := by
    obtain ⟨v, hv⟩ := htailev.exists
    have hpos : (0:ℝ) ≤ ∑ d ∈ (Finset.range v).filter (0 < ·), rankDropKer v d :=
      Finset.sum_nonneg (fun d _ => rankDropKer_nonneg v d)
    have h1 := le_trans hpos (hv 0)
    push_cast at h1
    have he : (0:ℝ) < Real.exp (-γ * (0:ℝ)) := Real.exp_pos _
    nlinarith [h1, he]
  have hεnn : ∀ A, 0 ≤ ε A := by
    intro A; rw [hεdef]
    have he : (0:ℝ) ≤ Real.exp (-γ * (A:ℝ)) := (Real.exp_pos _).le
    have hA1 : (0:ℝ) ≤ (A:ℝ) + 1 := by positivity
    positivity
  have hεsum : Summable ε := by
    rw [hεdef]
    have h1 : Summable (fun A : ℕ => ((A:ℝ) + 1) * Real.exp (-γ * (A:ℝ))) := by
      have hs := summable_pow_mul_exp_neg (c := γ) hγpos 1
      have hs0 := summable_pow_mul_exp_neg (c := γ) hγpos 0
      have : (fun A : ℕ => ((A:ℝ) + 1) * Real.exp (-γ * (A:ℝ)))
          = (fun A : ℕ => (A:ℝ)^1 * Real.exp (-γ*(A:ℝ))) + (fun A : ℕ => (A:ℝ)^0 * Real.exp (-γ*(A:ℝ))) := by
        funext A; simp [pow_one]; ring
      rw [this]; exact hs.add hs0
    exact (h1.mul_left C₀).congr (fun A => by ring)
  -- the subsolution β and its uniform floor α
  set β : ℕ → ℝ := betaSub ε η with hβ
  refine ⟨Real.exp (-(∑' j, ε j) / η), Real.exp_pos _, ?_⟩
  -- eventual-in-v facts: minorization, tail, mass
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.1 hηev
  obtain ⟨V₂, hV₂⟩ := eventually_atTop.1 htailev
  obtain ⟨V₃, hV₃⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set Vmax := max (max V₁ V₂) (max V₃ 10) with hVmax
  -- choose C large: any v with C < rnk v has v ≥ Vmax (via rnk_ge_of)
  refine eventually_atTop.2 ⟨max (3 * Vmax + 3) 1, fun C hC => ?_⟩
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  intro n hn
  -- the per-v hypotheses bundle
  have hfacts : ∀ v, C < rnk v →
      (1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
      ∧ η ≤ rankDropKer v 1
      ∧ (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => rnk v - C < d), rankDropKer v d
            ≤ ε (rnk v - C)) := by
    intro v hv
    have hvge : Vmax ≤ v := by
      apply rnk_ge_of (n₀ := Vmax)
      have : 3 * Vmax + 3 ≤ C := le_trans (le_max_left _ _) hC
      omega
    have hv10 : 10 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvge
    have hv2 : 2 ≤ v := by omega
    have hrltv : rnk v < v := rnk_lt_self hv10
    have hV1le : V₁ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hvge
    have hV2le : V₂ ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hvge
    have hV3le : V₃ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvge
    have hmin := hV₁ v hV1le
    have htail := hV₂ v hV2le (rnk v - C)
    have hSpos := hV₃ v hV3le
    refine ⟨?_, hmin.1, ?_⟩
    · rw [rankDropKer_total hv2 (ne_of_gt hSpos)]
    · -- overshoot tail over range(rnk v+1) = banked tail over range v (extra terms zero)
      refine le_trans (le_of_eq ?_) htail
      apply Finset.sum_subset
      · -- (range (rnk v+1)).filter ⊆ (range v).filter
        intro d hd
        rw [Finset.mem_filter, Finset.mem_range] at hd
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hd.2⟩
      · -- on (range v).filter \ (range (rnk v+1)).filter : rankDropKer = 0
        intro d hd hdnot
        rw [Finset.mem_filter, Finset.mem_range] at hd
        -- d ∈ range v with A < d but d ∉ range(rnk v+1).filter ⟹ rnk v < d
        have hdgt : rnk v < d := by
          by_contra hcon
          rw [not_lt] at hcon
          exact hdnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hd.2⟩)
        exact rankDropKer_eq_zero_of_gt hdgt
  -- run the subsolution comparison
  have hmain := ceilHit_ge_beta (C := C) (η := η) β ε hC1 hηpos.le
    (betaSub_antitone hηpos hεnn) (fun s => (betaSub_pos hηpos hεnn s).le)
    (by rw [hβ, betaSub_zero])
    (fun r hr => by rw [hβ]; exact le_of_eq (betaSub_slope hηpos hεnn hr))
    hfacts n hn
  -- β (rnk n − C) ≥ α
  have hβfloor : Real.exp (-(∑' j, ε j) / η) ≤ β (rnk n - C) := by
    rw [hβ]; exact betaSub_ge hηpos hεnn hεsum _
  calc Real.exp (-(∑' j, ε j) / η) ≤ β (rnk n - C) := hβfloor
    _ ≤ ceilHit C n := hmain
    _ = _ := rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK L4 (R8 elementary route): same-ceiling value overlap via the divisor-self bound `σ(m) ≥ m`

The variable rank-band engine needs a positive in-band overlap (L4): for two starts `x, y` at the
same ceiling rank `T = R + A R`, the first-entrance laws into the band `ceilBand R (A R)` overlap by
`≥ β` on the in-band slice `{R ≤ rnk z}`.  By the banked one-step reduction
`min_Pker_le_min_enterBandKer_sum` this reduces to a positive overlap of the **one-step** predecessor
laws `Pker x ·`, `Pker y ·` on the slice.

R8's elementary idea (`/tmp/ac_a_uniform.txt`): a single **common value window**
`W_T = [ (T+1)²/9 − 2T , T²/9 − T ] ∩ ℕ` (length `~7T/9`) sits below every ceiling-rank value `x`,
inside the engine slice, and carries `Pker x z ≥ c/T` for EVERY same-ceiling `x` and `z ∈ W_T`.
The lower bound uses ONLY the trivial divisor-self bound `σ(x−z) ≥ x−z ≥ T` (no two-point divisor
estimate, no `KernelWindow`).  A constant minorant `η = c/T` on `S = W_T` with `|W_T| ≥ q·T` gives
overlap `≥ (c/T)(q·T) = cq =: β > 0` via the banked `overlap_ge_of_minorization`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Brick 1 — the divisor-self bound `σ(m) ≥ m`. -/


/-! ## Brick 2 — the common value window. -/

/-! ## Brick 3 — window geometry: jump and sqrt bounds. -/


/-! ## Brick 4 — the window lies in the in-band slice. -/


/-! ## Brick 5 — pointwise `Pker` lower bound on the window. -/


/-! ## Brick 6 — linear cardinality of the window. -/


/-! ## Brick 7 — one-step same-ceiling value overlap. -/

/-- The ceiling rank `R ↦ R + A R` tends to `atTop` (since `R + A R ≥ R`). -/
lemma ceilRank_tendsto (A : ℕ → ℕ) : Tendsto (fun R => R + A R) atTop atTop :=
  tendsto_atTop_mono (fun R => Nat.le_add_right R (A R)) tendsto_id

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK T2-ceiling, L1: the mixture-overlap bridge

The ceiling-level regeneration route (ChatGPT R7) needs to convert
*pairwise* kernel overlap between level states into *mixture* overlap between the two
full entrance laws.  Concretely: if start `n` reaches the ceiling level with a sub-probability
weight `a : ℕ → ℝ` of total mass `≥ α`, start `n'` with weight `b` of total mass `≥ α`, the
continuation kernels `K x` are nonnegative, and any two level states `x, y` have continuation
overlap `≥ β` on the in-band `slice`, then the two mixtures
`A z = ∑_x a x · K x z` and `B z = ∑_y b y · K y z` overlap by `≥ α·β` on the slice.

**Proof (mixture convexity).**  Let `Sa = ∑_L a`, `Sb = ∑_L b` (both `≥ α ≥ 0`).  For each slice
state `z` define the doubly-weighted common mass
`W z = ∑_{x,y ∈ L} a x · b y · min (K x z) (K y z) ≥ 0`.  Then

* `W z ≤ ∑_{x,y} a x · b y · K x z = Sb · A z`, hence `W z / Sb ≤ A z`;
* `W z ≤ ∑_{x,y} a x · b y · K y z = Sa · B z`, hence `W z / Sa ≤ B z`;

so `min (A z) (B z) ≥ W z / max Sa Sb`.  Summing and using
`∑_z W z = ∑_{x,y} a x · b y · (∑_z min (K x z) (K y z)) ≥ β · Sa · Sb` gives
`∑_z min (A z) (B z) ≥ β · Sa · Sb / max Sa Sb = β · min Sa Sb ≥ α · β`.

NEW file; pure Finset algebra (imports only Mathlib).  Opus-authored.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **L1 — mixture-overlap bridge.**  See the file header for the statement and proof.  The
hypothesis `0 ≤ α` is necessary: with `α < 0` and a negative spurious overlap floor `β` the claim
`α·β ≤ ∑ min` is false (e.g. all data `0`, `α = β = -1`).  At the engine call site `α > 0`. -/
lemma overlap_of_mixtures_of_pairwise_overlap
    {L slice : Finset ℕ} {a b : ℕ → ℝ} {K : ℕ → ℕ → ℝ} {α β : ℝ}
    (hα : 0 ≤ α) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ y, 0 ≤ b y)
    (ha : α ≤ ∑ x ∈ L, a x) (hb : α ≤ ∑ y ∈ L, b y)
    (hK0 : ∀ x z, 0 ≤ K x z)
    (hpair : ∀ x ∈ L, ∀ y ∈ L, β ≤ ∑ z ∈ slice, min (K x z) (K y z)) :
    α * β ≤ ∑ z ∈ slice, min (∑ x ∈ L, a x * K x z) (∑ y ∈ L, b y * K y z) := by
  classical
  set Sa : ℝ := ∑ x ∈ L, a x with hSa
  set Sb : ℝ := ∑ y ∈ L, b y with hSb
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg (fun x _ => ha0 x)
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun y _ => hb0 y)
  set A : ℕ → ℝ := fun z => ∑ x ∈ L, a x * K x z with hAdef
  set B : ℕ → ℝ := fun z => ∑ y ∈ L, b y * K y z with hBdef
  set W : ℕ → ℝ := fun z => ∑ x ∈ L, ∑ y ∈ L, a x * b y * min (K x z) (K y z) with hWdef
  have hW0 : ∀ z, 0 ≤ W z := by
    intro z
    refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_))
    exact mul_nonneg (mul_nonneg (ha0 x) (hb0 y)) (le_min (hK0 x z) (hK0 y z))
  -- W z ≤ Sb · A z
  have hWA : ∀ z, W z ≤ Sb * A z := by
    intro z
    have hstep : W z ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z := by
      refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg (ha0 x) (hb0 y))
    have hcollapse : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z) = Sb * A z := by
      have hper : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z) = ∑ x ∈ L, (a x * K x z) * Sb := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hSb, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => by ring)
      rw [hper, ← Finset.sum_mul, hAdef]; ring
    rw [← hcollapse]; exact hstep
  -- W z ≤ Sa · B z
  have hWB : ∀ z, W z ≤ Sa * B z := by
    intro z
    have hstep : W z ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * K y z := by
      refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (ha0 x) (hb0 y))
    have hcollapse : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K y z) = Sa * B z := by
      rw [Finset.sum_comm]
      have : (∑ y ∈ L, ∑ x ∈ L, a x * b y * K y z) = ∑ y ∈ L, Sa * (b y * K y z) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hSa, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => by ring)
      rw [this, ← Finset.mul_sum, hBdef]
    rw [← hcollapse]; exact hstep
  -- ∑_z W z ≥ β · Sa · Sb
  have hWsum : β * Sa * Sb ≤ ∑ z ∈ slice, W z := by
    have hWsum_eq : (∑ z ∈ slice, W z)
        = ∑ x ∈ L, ∑ y ∈ L, a x * b y * (∑ z ∈ slice, min (K x z) (K y z)) := by
      rw [hWdef]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum]
    rw [hWsum_eq]
    -- lower-bound each pairwise overlap by β, then collapse ∑ a · ∑ b
    have hlb : ∑ x ∈ L, ∑ y ∈ L, a x * b y * β
        ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * (∑ z ∈ slice, min (K x z) (K y z)) := by
      refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => ?_))
      exact mul_le_mul_of_nonneg_left (hpair x hx y hy) (mul_nonneg (ha0 x) (hb0 y))
    refine le_trans ?_ hlb
    -- ∑_x ∑_y a x b y β = β Sa Sb
    have hconst : (∑ x ∈ L, ∑ y ∈ L, a x * b y * β) = β * Sa * Sb := by
      have e1 : (∑ x ∈ L, ∑ y ∈ L, a x * b y * β)
          = ∑ x ∈ L, (a x * (∑ y ∈ L, b y) * β) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [e1, ← Finset.sum_mul, ← Finset.sum_mul, hSa, hSb]; ring
    rw [hconst]
  -- A, B nonneg pointwise
  have hAz : ∀ z, 0 ≤ A z := fun z => Finset.sum_nonneg (fun x _ => mul_nonneg (ha0 x) (hK0 x z))
  have hBz : ∀ z, 0 ≤ B z := fun z => Finset.sum_nonneg (fun y _ => mul_nonneg (hb0 y) (hK0 y z))
  have hsum_nonneg : 0 ≤ ∑ z ∈ slice, min (A z) (B z) :=
    Finset.sum_nonneg (fun z _ => le_min (hAz z) (hBz z))
  -- split on the sign of β: β ≤ 0 makes the claim trivial.
  rcases le_or_gt β 0 with hβ | hβpos
  · -- α ≥ 0, β ≤ 0 ⟹ α·β ≤ 0 ≤ ∑ min
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hα hβ) hsum_nonneg
  · -- β > 0.  Now Sa, Sb > 0 (else β·Sa·Sb ≤ 0 < ... contradicts hWsum giving W≥0 fine, but we
    -- need the division; handle Sa or Sb = 0 by trivial bound too).
    rcases eq_or_lt_of_le hSa0 with hSaz | hSapos
    · -- Sa = 0 ⟹ α ≤ 0, with hα gives α = 0
      have hαz : α = 0 := le_antisymm (le_trans ha (le_of_eq hSaz.symm)) hα
      rw [hαz, zero_mul]; exact hsum_nonneg
    rcases eq_or_lt_of_le hSb0 with hSbz | hSbpos
    · have hαz : α = 0 := le_antisymm (le_trans hb (le_of_eq hSbz.symm)) hα
      rw [hαz, zero_mul]; exact hsum_nonneg
    set D : ℝ := max Sa Sb with hDdef
    have hDpos : 0 < D := lt_of_lt_of_le hSapos (le_max_left _ _)
    -- min (A z) (B z) ≥ W z / D
    have hkey : ∀ z, W z / D ≤ min (A z) (B z) := by
      intro z
      refine le_min ?_ ?_
      · rw [div_le_iff₀ hDpos]
        refine le_trans (hWA z) ?_
        calc Sb * A z ≤ D * A z := mul_le_mul_of_nonneg_right (le_max_right Sa Sb) (hAz z)
          _ = A z * D := by ring
      · rw [div_le_iff₀ hDpos]
        refine le_trans (hWB z) ?_
        calc Sa * B z ≤ D * B z := mul_le_mul_of_nonneg_right (le_max_left Sa Sb) (hBz z)
          _ = B z * D := by ring
    have hsumlb : (∑ z ∈ slice, W z) / D ≤ ∑ z ∈ slice, min (A z) (B z) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun z _ => hkey z)
    refine le_trans ?_ hsumlb
    rw [le_div_iff₀ hDpos]
    refine le_trans ?_ hWsum
    -- goal: α * β * D ≤ β * Sa * Sb.  Use Sa*Sb = D * min Sa Sb and α ≤ min Sa Sb, β > 0.
    have hSaSb : Sa * Sb = D * min Sa Sb := by
      rcases le_total Sa Sb with h | h
      · rw [hDdef, max_eq_right h, min_eq_left h]; ring
      · rw [hDdef, max_eq_left h, min_eq_right h]
    have hminαβ : α ≤ min Sa Sb := le_min ha hb
    have hβD : 0 ≤ β * D := mul_nonneg hβpos.le hDpos.le
    calc α * β * D = (β * D) * α := by ring
      _ ≤ (β * D) * min Sa Sb := mul_le_mul_of_nonneg_left hminαβ hβD
      _ = β * Sa * Sb := by rw [show β * Sa * Sb = β * (Sa * Sb) by ring, hSaSb]; ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK L5 (part 1): the composed in-band overlap `δ = α·β`

Composes the banked ceiling-level regeneration bricks into the **in-band overlap** required by the
variable rank-band engine (`hitVal_cauchy_of_ceilBand_overlap_escape_variable`):

  `α·β ≤ ∑_{z ∈ slice} min (enterBandKer Pker B n z) (enterBandKer Pker B n' z)`,

for `B = ceilBand R (A R)`, `C := R + A R`, `slice = B.filter (R ≤ rnk ·)`, and any two starts
`n, n'` of rank `≥ C`.

Mechanism (ChatGPT R7 ceiling route):
* **L3** (`Pker_hit_ceiling_level_mass_lower`): each start hits the ceiling **level** `{rnk = C}` with
  first-entrance mass `≥ α` (`ceilHit C n ≥ α`).
* **L2** (`enterBandKer_factor_through_ceiling_level`): the level-mixture
  `∑_{x ∈ L} (enterBandKer (ceilBand C 1) n x) · (enterBandKer B x z)` lower-bounds the true entrance
  law `enterBandKer B n z`.
* **L4** (`same_ceiling_enterBand_overlap`): any two level states `x, y` (both `rnk = C`) overlap by
  `≥ β` on the slice.
* **L1** (`overlap_of_mixtures_of_pairwise_overlap`): the two level-mixtures overlap by `≥ α·β`;
  since each mixture lower-bounds the true entrance law, so does the min — `δ = α·β`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 1000000 in
/-- **Composed in-band overlap (`δ = α·β`).**  There is `δ > 0` so that eventually in `R`, for any two
starts `n, n'` of rank `≥ R + A R`, the first-entrance laws into `B = ceilBand R (A R)` overlap by
`≥ δ` on the in-band slice `{R ≤ rnk z}`.  Composition of L1–L4. -/
lemma Pker_ceilBand_inband_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ R in atTop, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
        δ ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (A R)) n z)
                  (enterBandKer Pker (ceilBand R (A R)) n' z) := by
  obtain ⟨α, hαpos, hαev⟩ := Pker_hit_ceiling_level_mass_lower
  obtain ⟨β, hβpos, hβev⟩ := same_ceiling_enterBand_overlap A hA
  refine ⟨α * β, by positivity, ?_⟩
  have htend := ceilRank_tendsto A
  -- L3 pulled to R (ceiling floor C = R + A R)
  have hαR : ∀ᶠ R in atTop, ∀ n, (R + A R) ≤ rnk n →
      α ≤ ∑ x ∈ (ceilBand (R + A R) 1).filter (fun x => (R + A R) ≤ rnk x),
            enterBandKer Pker (ceilBand (R + A R) 1) n x := htend.eventually hαev
  filter_upwards [hαR, hβev] with R hα hβ
  intro n n' hn hn'
  set C := R + A R with hCdef
  set B := ceilBand R (A R) with hBdef
  set L := (ceilBand C 1).filter (fun x => C ≤ rnk x) with hLdef
  -- weights a, b (ceiling-level entrance from n, n') and continuation kernel K
  set a : ℕ → ℝ := fun x => enterBandKer Pker (ceilBand C 1) n x with hadef
  set b : ℕ → ℝ := fun x => enterBandKer Pker (ceilBand C 1) n' x with hbdef
  set K : ℕ → ℕ → ℝ := fun x z => enterBandKer Pker B x z with hKdef
  -- L3: total level mass ≥ α
  have haL : α ≤ ∑ x ∈ L, a x := hα n hn
  have hbL : α ≤ ∑ x ∈ L, b x := hα n' hn'
  -- nonnegativity
  have ha0 : ∀ x, 0 ≤ a x := fun x => enterBandKer_nonneg (fun p q => Pker_nonneg p q) n x
  have hb0 : ∀ x, 0 ≤ b x := fun x => enterBandKer_nonneg (fun p q => Pker_nonneg p q) n' x
  have hK0 : ∀ x z, 0 ≤ K x z := fun x z => enterBandKer_nonneg (fun p q => Pker_nonneg p q) x z
  -- L4: pairwise overlap on slice for any two level states (rnk = C)
  have hpair : ∀ x ∈ L, ∀ y ∈ L,
      β ≤ ∑ z ∈ B.filter (fun z => R ≤ rnk z), min (K x z) (K y z) := by
    intro x hx y hy
    have hxrnk : rnk x = C := by
      have := Finset.mem_filter.mp hx
      have hlt := mem_ceilBand_iff.mp this.1
      have hge := this.2
      omega
    have hyrnk : rnk y = C := by
      have := Finset.mem_filter.mp hy
      have hlt := mem_ceilBand_iff.mp this.1
      have hge := this.2
      omega
    exact hβ x y hxrnk hyrnk
  -- L1: mixture overlap ≥ α·β
  have hmix := overlap_of_mixtures_of_pairwise_overlap
    (L := L) (slice := B.filter (fun z => R ≤ rnk z)) (a := a) (b := b) (K := K)
    (α := α) (β := β) hαpos.le ha0 hb0 haL hbL hK0 hpair
  -- L2: each mixture lower-bounds the true entrance law, pointwise on the slice
  refine le_trans hmix ?_
  apply Finset.sum_le_sum
  intro z _hz
  apply min_le_min
  · -- ∑_{x∈L} a x · K x z ≤ enterBandKer B n z
    exact enterBandKer_factor_through_ceiling_level R A n z hn
  · exact enterBandKer_factor_through_ceiling_level R A n' z hn'

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Ceiling-escape brick 4 (THE KEY BRICK): the abstract additive escape super-solution

This is the deterministic core of the elementary close (R9).  It replaces the conditional-ratio
strategy of `enterBand_deep_mass_le_of_conditional` by a **direct additive super-solution** driven by
the banked drop-1 minorization `η` and the banked deep-mass tail majorant `U`.

For the first-entrance kernel into the ceiling down-set `B = ceilBand R A`, the overshoot below the
band floor `R` from any off-band start `n` satisfies the finite super-solution

  `esc(n) ≤ E(g(n))`,   `E(g) = (1/η)·∑_{i∈range(g+1)} U(A+i)`,   `g(v) = rnk v − (R+A)`,

proved by strong induction on `n`.  The mechanism (R9): one off-band step splits into deep crossing
(`≤ U(A+g)` by `hdeep`), safe crossing (lands in-band, not deep), and off-band continuation (IH).
The drop-1 mass `≥ η` either shifts `g → g−1` (when `g > 0`), and `η·(E(g)−E(g−1)) = U(A+g)` pays the
deep forcing exactly, or — when `g = 0` — crosses safely into the band, removing `≥ η` from the
off-band continuation, and `η·E(0) = U(A)` again pays the forcing.

Since `E(g) ≤ (1/η)·∑'_i U(A+i)`, this drives the overshoot to `0` once the band floor `R → ∞`
(brick 5).

NEW file; imports the banked engine bricks; does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 4 — abstract additive escape super-solution (finite form).**

Let `P ≥ 0` be a sub-stochastic predecessor kernel supported on `k < v`, row-stochastic off the
ceiling band `B = ceilBand R A`.  Suppose, at every off-band vertex `v`:

* (deep) the one-step deep-crossing mass (landing in `B` below rank `R`) is `≤ U (A + g v)`, where
  `g v = rnk v − (R + A)`;
* (drop-1) the rank-drop-exactly-1 mass is `≥ η`.

With `U ≥ 0` and `η > 0`, the first-entrance overshoot below `R` from any off-band start `n`
satisfies `esc(n) ≤ E (g n)`, `E g = (1/η)·∑_{i∈range(g+1)} U (A+i)`. -/
theorem enterBand_deep_mass_le_of_tail_forcing_drop_one
    {P : ℕ → ℕ → ℝ} {R A : ℕ} {U : ℕ → ℝ} {η : ℝ}
    (hη : 0 < η) (hU0 : ∀ t, 0 ≤ U t)
    (hPnn : ∀ n k, 0 ≤ P n k)
    (hPsupp : ∀ m k, m ≤ k → P m k = 0)
    (hrow : ∀ v, v ∉ ceilBand R A → ∑ k ∈ Finset.range v, P v k = 1)
    (hdeep : ∀ v, v ∉ ceilBand R A →
        (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), P v k)
          ≤ U (A + (rnk v - (R + A))))
    (hdrop1 : ∀ v, v ∉ ceilBand R A →
        η ≤ ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = 1), P v k) :
    ∀ n, n ∉ ceilBand R A →
      (∑ z ∈ (ceilBand R A).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer P (ceilBand R A) n z)
        ≤ (1 / η) * ∑ i ∈ Finset.range ((rnk n - (R + A)) + 1), U (A + i) := by
  classical
  set B := ceilBand R A with hBdef
  -- the potential E g
  set E : ℕ → ℝ := fun g => (1 / η) * ∑ i ∈ Finset.range (g + 1), U (A + i) with hEdef
  -- esc' k : deep first-entrance mass from k
  set esc : ℕ → ℝ := fun k => ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer P B k z with hescdef
  set g : ℕ → ℕ := fun v => rnk v - (R + A) with hgdef
  -- basic facts about E
  have hEnn : ∀ m, 0 ≤ E m := by
    intro m; simp only [hEdef]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => hU0 _)
  have hEmono : ∀ {m m' : ℕ}, m ≤ m' → E m ≤ E m' := by
    intro m m' hmm
    simp only [hEdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact hU0 _
  -- E g − E (g−1) = (1/η)·U(A+g) for g ≥ 1
  have hEdiff : ∀ m : ℕ, 1 ≤ m → E m - E (m - 1) = (1 / η) * U (A + m) := by
    intro m hm
    simp only [hEdef]
    have hmsucc : (m - 1) + 1 = m := by omega
    have hsplit : ∑ i ∈ Finset.range (m + 1), U (A + i)
        = (∑ i ∈ Finset.range ((m - 1) + 1), U (A + i)) + U (A + m) := by
      rw [hmsucc, Finset.sum_range_succ]
    rw [hsplit]; ring
  -- E 0 = (1/η)·U(A)
  have hE0 : E 0 = (1 / η) * U (A + 0) := by
    rw [hEdef]; simp
  -- the goal reduced to esc n ≤ E (g n)
  suffices hmain : ∀ n, n ∉ B → esc n ≤ E (g n) by exact hmain
  -- main strong induction
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    -- expand esc n over range n
    have hexpand : ∀ z, enterBandKer P B n z
        = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
      intro z; rw [enterBandKer_eq, if_neg hn]
    have hescn : esc n = ∑ k ∈ Finset.range n, P n k * esc k := by
      simp only [hescdef]
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    -- off-band n facts
    have hrnkn : rnk n = R + A + g n := by
      have := not_mem_ceilBand_rank_ge hn; simp only [hgdef]; omega
    -- esc k for in-band k : point mass at k, deep iff ¬ R ≤ rnk k
    have hesc_inband : ∀ k, k ∈ B → esc k = if ¬ R ≤ rnk k then (1:ℝ) else 0 := by
      intro k hk
      simp only [hescdef]
      have hval : ∀ z, enterBandKer P B k z = if z = k then 1 else 0 := by
        intro z; rw [enterBandKer_eq, if_pos hk]
      rw [Finset.sum_congr rfl (fun z _ => hval z)]
      by_cases hkd : ¬ R ≤ rnk k
      · rw [if_pos hkd, Finset.sum_ite_eq' (B.filter (fun z => ¬ R ≤ rnk z)) k (fun _ => (1:ℝ)),
          if_pos (Finset.mem_filter.mpr ⟨hk, hkd⟩)]
      · rw [if_neg hkd]
        refine Finset.sum_eq_zero (fun z hz => ?_)
        rw [if_neg]; rintro rfl; exact hkd (Finset.mem_filter.mp hz).2
    -- pointwise bound esc k ≤ φ k on range n
    set φ : ℕ → ℝ := fun k => if k ∈ B then (if ¬ R ≤ rnk k then (1:ℝ) else 0) else E (g k)
      with hφdef
    have hesc_le : ∀ k ∈ Finset.range n, esc k ≤ φ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [hφdef]
      by_cases hkB : k ∈ B
      · rw [if_pos hkB, hesc_inband k hkB]
      · rw [if_neg hkB]; exact ih k hk hkB
    -- ∑ P n k · esc k ≤ ∑ P n k · φ k
    have hstep1 : esc n ≤ ∑ k ∈ Finset.range n, P n k * φ k := by
      rw [hescn]
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hesc_le k hk) (hPnn n k)
    -- split range n into in-band / off-band predecessors
    have hsplit : ∑ k ∈ Finset.range n, P n k * φ k
        = (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
          + ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * φ k := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k ∈ B)]
    -- in-band part = deep in-band mass = ∑_{B.filter deep} P n k ≤ U (A + g n)
    have hinband : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        = ∑ k ∈ B.filter (fun k => ¬ R ≤ rnk k), P n k := by
      -- φ k = [deep k] for k ∈ B; then extend the index set (P n k = 0 off range n)
      have hval : ∀ k ∈ (Finset.range n).filter (fun k => k ∈ B),
          P n k * φ k = if ¬ R ≤ rnk k then P n k else 0 := by
        intro k hk
        have hkB : k ∈ B := (Finset.mem_filter.mp hk).2
        simp only [hφdef, if_pos hkB]
        by_cases hkd : ¬ R ≤ rnk k <;> simp [hkd]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      apply Finset.sum_subset_zero_on_sdiff
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
        exact Finset.mem_filter.mpr ⟨hk.1.2, hk.2⟩
      · intro k hk
        rw [Finset.mem_sdiff, Finset.mem_filter] at hk
        have hkn : n ≤ k := by
          by_contra h; push_neg at h
          exact hk.2 (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr h, hk.1.1⟩, hk.1.2⟩)
        exact hPsupp n k hkn
      · intro k _; rfl
    have hinband_le : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        ≤ U (A + g n) := by
      rw [hinband]; exact hdeep n hn
    -- off-band part written with E(g k)
    have hoffval : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B),
        P n k * φ k = P n k * E (g k) := by
      intro k hk
      have hkB : k ∉ B := (Finset.mem_filter.mp hk).2
      simp only [hφdef, if_neg hkB]
    rw [hsplit, Finset.sum_congr rfl hoffval] at hstep1
    -- Now: esc n ≤ inband + ∑_{offband} P n k · E(g k); bound inband ≤ U(A+g n)
    set Soff := ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k with hSoffdef
    -- each off-band k<n: rnk k ≤ rnk n, k ∉ B so rnk k ≥ R+A, hence g k ≤ g n
    have hgk_le : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B), g k ≤ g n := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      have hrnkkle : rnk k ≤ rnk n := rnk_mono hk.1.le
      simp only [hgdef]; omega
    -- row-sum bound : Soff ≤ 1
    have hSoff_le_one : Soff ≤ 1 := by
      rw [hSoffdef, ← hrow n hn]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; exact (Finset.mem_filter.mp hk).1
      · intro k _ _; exact hPnn n k
    have hSoff_nn : 0 ≤ Soff := Finset.sum_nonneg (fun k _ => hPnn n k)
    -- the drop-1 mass over range n (banked ≥ η)
    set Drop1 := ∑ k ∈ (Finset.range n).filter (fun k => rnk n - rnk k = 1), P n k with hDrop1def
    have hDrop1_ge : η ≤ Drop1 := by
      rw [hDrop1def]; exact hdrop1 n hn
    have hDrop1_nn : 0 ≤ Drop1 := Finset.sum_nonneg (fun k _ => hPnn n k)
    -- It suffices: U(A+g n) + (off-band E-sum) ≤ E (g n)
    have hoffsum_def : True := trivial
    refine le_trans hstep1 ?_
    -- abbreviate the off-band E-sum
    set OffE := ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * E (g k) with hOffEdef
    refine le_trans (by linarith [hinband_le] :
        (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        + OffE ≤ U (A + g n) + OffE) ?_
    -- now goal: U (A + g n) + OffE ≤ E (g n)
    rcases Nat.eq_zero_or_pos (g n) with hg0 | hgpos
    · -- CASE g n = 0
      -- every off-band k<n has g k = 0 (rnk k = R+A); so OffE = Soff · E 0
      have hgk0 : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B), g k = 0 := by
        intro k hk
        have hle := hgk_le k hk
        omega
      have hOffE_eq : OffE = Soff * E 0 := by
        rw [hOffEdef, hSoffdef, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hgk0 k hk]
      -- drop-1 predecessors are in-band (rnk = rnk n - 1 = R+A-1 < R+A), disjoint from off-band
      -- so Soff + Drop1 ≤ row-sum = 1, hence Soff ≤ 1 - η
      have hdisj : Disjoint ((Finset.range n).filter (fun k => k ∉ B))
          ((Finset.range n).filter (fun k => rnk n - rnk k = 1)) := by
        rw [Finset.disjoint_left]
        intro k hkoff hkd1
        rw [Finset.mem_filter] at hkoff hkd1
        have hkB : k ∉ B := hkoff.2
        have hd1 : rnk n - rnk k = 1 := hkd1.2
        -- rnk k = rnk n - 1 = R + A - 1 < R + A ⟹ k ∈ B, contradiction
        have hkn : k < n := Finset.mem_range.mp hkoff.1
        have hrnkkle : rnk k ≤ rnk n := rnk_mono hkn.le
        have : rnk k < R + A := by rw [hrnkn, hg0] at hd1 hrnkkle; omega
        exact hkB (mem_ceilBand_iff.mpr this)
      have hSD_le : Soff + Drop1 ≤ 1 := by
        rw [hSoffdef, hDrop1def, ← Finset.sum_union hdisj, ← hrow n hn]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_union] at hk
          rcases hk with h | h
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
        · intro k _ _; exact hPnn n k
      have hSoff_le : Soff ≤ 1 - η := by linarith [hDrop1_ge, hSD_le]
      -- assemble: U(A+0) + Soff·E0 ≤ U(A+0) + (1-η)E0 = E0 ; and goal RHS = E (g n) = E 0
      have hgnE : E (g n) = E 0 := by rw [hg0]
      rw [hOffE_eq, hgnE, hE0, hg0]
      -- goal: U (A + 0) + Soff * ((1/η)*U(A+0)) ≤ (1/η)*U(A+0)
      have hUA0 : 0 ≤ U (A + 0) := hU0 _
      have hηE0 : η * ((1 / η) * U (A + 0)) = U (A + 0) := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hSoff_le
          (by positivity : (0:ℝ) ≤ (1 / η) * U (A + 0)), hηE0, hUA0, hη]
    · -- CASE g n ≥ 1
      -- per-term bound on off-band k: E (g k) ≤ E (g n) − [drop1 k]·(E (g n) − E (g n − 1))
      set diff := E (g n) - E (g n - 1) with hdiffdef
      have hdiff_eq : η * diff = U (A + g n) := by
        rw [hdiffdef, hEdiff (g n) hgpos]; field_simp
      have hdiff_nn : 0 ≤ diff := by rw [hdiffdef]; linarith [hEmono (Nat.sub_le (g n) 1)]
      -- drop1 ⊆ off-band (in case g n ≥ 1)
      have hsubD : (Finset.range n).filter (fun k => rnk n - rnk k = 1)
          ⊆ (Finset.range n).filter (fun k => k ∉ B) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        have hd1 : rnk n - rnk k = 1 := hk.2
        have hkn : k < n := Finset.mem_range.mp hk.1
        have hrnkkle : rnk k ≤ rnk n := rnk_mono hkn.le
        -- rnk k = rnk n - 1 = R+A+g n - 1 ≥ R+A (since g n ≥ 1) ⟹ k ∉ B
        have : R + A ≤ rnk k := by rw [hrnkn] at hd1 hrnkkle; omega
        intro hcon; exact (Nat.not_le.mpr (mem_ceilBand_iff.mp hcon)) this
      -- OffE ≤ Soff·E(g n) − Drop1·diff
      have hOffE_le : OffE ≤ Soff * E (g n) - Drop1 * diff := by
        -- split off-band by drop1
        have hsp : (∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * E (g k))
            = (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => rnk n - rnk k = 1), P n k * E (g k))
              + ∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k) := by
          rw [← Finset.sum_filter_add_sum_filter_not
            ((Finset.range n).filter (fun k => k ∉ B)) (fun k => rnk n - rnk k = 1)]
        rw [hOffEdef, hsp]
        -- drop1-part: E (g k) = E (g n − 1)
        have hpart1 : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => rnk n - rnk k = 1), P n k * E (g k))
            = Drop1 * E (g n - 1) := by
          rw [hDrop1def, Finset.sum_mul]
          -- the two index sets coincide (drop1 ⊆ off-band), and E(g k)=E(g n−1)
          have hidx : ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => rnk n - rnk k = 1)
              = (Finset.range n).filter (fun k => rnk n - rnk k = 1) := by
            apply Finset.filter_comm _ _ _ |>.trans
            apply Finset.filter_eq_self.mpr
            intro k hk
            have := hsubD hk
            exact (Finset.mem_filter.mp this).2
          rw [hidx]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_filter, Finset.mem_range] at hk
          have hd1 : rnk n - rnk k = 1 := hk.2
          have hrnkkle : rnk k ≤ rnk n := rnk_mono hk.1.le
          have hgkeq : g k = g n - 1 := by simp only [hgdef]; rw [hrnkn] at *; omega
          rw [hgkeq]
        rw [hpart1]
        -- non-drop1 part: E (g k) ≤ E (g n)
        have hpart2 : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k))
            ≤ (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkoff : k ∈ (Finset.range n).filter (fun k => k ∉ B) :=
            (Finset.mem_filter.mp hk).1
          exact mul_le_mul_of_nonneg_left (hEmono (hgk_le k hkoff)) (hPnn n k)
        -- Soff = drop1-mass + non-drop1-mass (within off-band)
        have hSoff_split : Soff
            = Drop1 + ∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => ¬ rnk n - rnk k = 1), P n k := by
          rw [hSoffdef,
            ← Finset.sum_filter_add_sum_filter_not
              ((Finset.range n).filter (fun k => k ∉ B)) (fun k => rnk n - rnk k = 1)]
          congr 1
          rw [hDrop1def]
          have hidx : ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => rnk n - rnk k = 1)
              = (Finset.range n).filter (fun k => rnk n - rnk k = 1) := by
            apply Finset.filter_comm _ _ _ |>.trans
            apply Finset.filter_eq_self.mpr
            intro k hk
            have := hsubD hk
            exact (Finset.mem_filter.mp this).2
          rw [hidx]
        -- assemble
        have hnon_eq : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n))
            = (Soff - Drop1) * E (g n) := by
          rw [hSoff_split]; rw [← Finset.sum_mul]; ring_nf
        calc Drop1 * E (g n - 1)
              + (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k))
            ≤ Drop1 * E (g n - 1)
              + (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n)) := by linarith [hpart2]
          _ = Drop1 * E (g n - 1) + (Soff - Drop1) * E (g n) := by rw [hnon_eq]
          _ = Soff * E (g n) - Drop1 * diff := by rw [hdiffdef]; ring
      -- final: U(A+g n) + OffE ≤ U(A+g n) + Soff·E(g n) − Drop1·diff ≤ E(g n)
      have hDdiff : U (A + g n) ≤ Drop1 * diff := by
        rw [← hdiff_eq]; exact mul_le_mul_of_nonneg_right hDrop1_ge hdiff_nn
      have hSE : Soff * E (g n) ≤ E (g n) := by
        nlinarith [mul_le_mul_of_nonneg_right hSoff_le_one (hEnn (g n)), hEnn (g n)]
      linarith [hOffE_le, hDdiff, hSE]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK L5 (part 2): the ceiling-route assembly into `erdos_partition_limit_exists`

This file wires the ceiling-level regeneration route through the variable rank-band engine
`hitVal_cauchy_of_ceilBand_overlap_escape_variable`.  The growing band width is
`A R = 1 + ⌊√(R+1)⌋` (unbounded, sublinear, positive).  The engine's overlap input is the banked
composed in-band overlap `Pker_ceilBand_inband_overlap` (δ = α·β, R8 elementary route via σ≥m).

The engine's remaining input is the **escape** (overshoot below the band floor `R` vanishes):

  `∀ᶠ R, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
      (∑_{z ∈ B, rnk z < R} enterBandKer Pker B n z ≤ e R)
    ∧ (∑_{z ∈ B, rnk z < R} enterBandKer Pker B n' z ≤ e R)`,   `B = ceilBand R (A R)`, `e R → 0`.

`erdos_partition_limit_exists_of_escape` produces the unconditional limit **from** this escape pair;
the escape itself is the single genuine remaining analytic input (a matching-constant geometric
rank-drop tail two-sided bound).

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The growing band width `A R = 1 + ⌊√(R+1)⌋`. -/
def ceilA (R : ℕ) : ℕ := 1 + Nat.sqrt (R + 1)

lemma ceilA_pos (R : ℕ) : 1 ≤ ceilA R := by unfold ceilA; omega

lemma ceilA_tendsto : Tendsto ceilA atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, fun R hR => ?_⟩
  unfold ceilA
  have hsq : b ≤ Nat.sqrt (R + 1) := by
    rw [Nat.le_sqrt]; omega
  omega

/-- `A R = 1 + ⌊√(R+1)⌋ ≤ R/2` eventually (√ grows sublinearly). -/
lemma ceilA_sublinear : ∀ᶠ R in atTop, ceilA R ≤ R / 2 := by
  filter_upwards [eventually_ge_atTop 64] with R hR
  unfold ceilA
  -- √(R+1) ≤ R/4 (since (R/4)² ≥ R+1 for R ≥ 64), then 1 + R/4 ≤ R/2
  have hsqr_lb : R + 1 ≤ (R / 4) * (R / 4) := by
    have h1 : 16 ≤ R / 4 := by omega
    have h2 : 4 * (R / 4) + 3 ≥ R := by omega
    nlinarith [h1, h2]
  have hsqrt : Nat.sqrt (R + 1) ≤ R / 4 := by
    have h := Nat.sqrt_le_sqrt hsqr_lb
    rwa [Nat.sqrt_eq] at h
  omega

lemma ceilA_pos_eventually : ∀ᶠ R in atTop, 1 ≤ ceilA R :=
  Eventually.of_forall ceilA_pos

/-- **The ceiling-route escape hypothesis.**  The first-entrance overshoot below the band floor `R`
into `B = ceilBand R (A R)` vanishes: there is `e R → 0` (nonneg) bounding the deep mass from any two
high starts.  This is the single genuine remaining analytic input of the ceiling route (L5-escape). -/
def CeilingEscape : Prop :=
  ∃ e : ℕ → ℝ, (∀ R, 0 ≤ e R) ∧ Tendsto e atTop (𝓝 0) ∧
    ∀ᶠ R in atTop, ∀ n n', R + ceilA R ≤ rnk n → R + ceilA R ≤ rnk n' →
      (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer Pker (ceilBand R (ceilA R)) n z ≤ e R)
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer Pker (ceilBand R (ceilA R)) n' z ≤ e R)

/-- **The Hardy–Ramanujan partition-ratio limit, modulo the ceiling escape.**  If the first-entrance
overshoot below the band floor vanishes (`CeilingEscape`), then the normalized partition sequence `u`
converges to a positive limit.  Everything else — the in-band overlap `δ = α·β` (R8 elementary route,
`Pker_ceilBand_inband_overlap`), the variable-band Doeblin engine, and the harmonic-hit reduction —
is banked clean-3. -/
theorem erdos_partition_limit_exists_of_escape (hesc : CeilingEscape) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨e, he0, hetend, hescev⟩ := hesc
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨δ, hδpos, hδev⟩ := Pker_ceilBand_inband_overlap ceilA ceilA_tendsto
  -- normalize δ ≤ 1 for the engine (cap at 1)
  set δ' := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  -- kernelMass ≠ 0 for high rank
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkmR : ∀ {J : ℕ}, 3 * N₀ + 3 ≤ J → ∀ m, J ≤ rnk m → kernelMass m ≠ 0 := by
    intro J hJ m hm
    have hge : N₀ ≤ m := rnk_ge_of (le_trans hJ hm)
    exact ne_of_gt (hN₁ m (le_trans (le_max_left _ _) hge))
  -- the engine's combined overlap+escape, for the fixed band width A = ceilA
  have hcombined : ∀ᶠ R in atTop, ∀ n n', R + ceilA R ≤ rnk n → R + ceilA R ≤ rnk n' →
      (δ' ≤ ∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (ceilA R)) n z)
                  (enterBandKer Pker (ceilBand R (ceilA R)) n' z))
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
              enterBandKer Pker (ceilBand R (ceilA R)) n z ≤ e R)
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
              enterBandKer Pker (ceilBand R (ceilA R)) n' z ≤ e R) := by
    filter_upwards [hδev, hescev] with R hov hesc
    intro n n' hn hn'
    obtain ⟨hesc1, hesc2⟩ := hesc n n' hn hn'
    exact ⟨le_trans hδ'le (hov n n' hn hn'), hesc1, hesc2⟩
  -- feed the variable engine for every cutoff J ≥ 3 N₀ + 3 ⟹ hhit
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [eventually_ge_atTop (3 * N₀ + 3)] with J hJ
  refine hitVal_cauchy_of_ceilBand_overlap_escape_variable
    (J := J) (φ := u) (δ := δ') (Mφ := Mu) (e := e) (A := ceilA)
    ceilA_tendsto ceilA_sublinear ceilA_pos_eventually
    hδ'pos hδ'1 hMu0 hMu he0 hetend ?_ ?_ hcombined
  · -- hharm : J ≤ rnk m ⟹ hitVal harmonic at m
    intro m hm
    rw [hitVal_eq, if_neg (by omega)]
  · -- hkm : J ≤ rnk m ⟹ kernelMass m ≠ 0
    intro m hm
    exact hkmR hJ m hm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Ceiling-escape brick 1: the rank-drop tail majorant as a clean summable sequence

This file packages the banked rank-drop tail majorant `C₀·(t+1)·e^{−γt}` (the upper bound of
`Pker_rankDrop_tail_majorant`) as a reusable nonnegative, summable sequence with a vanishing shifted
tail.  It is pure exponential-polynomial summability — no analytic number theory, no `Pker`.

* `rankDropTailMaj γ C₀ t = C₀·(t+1)·e^{−γt}`  (nonneg for `C₀ ≥ 0`);
* `rankDropTailMaj_summable` (for `γ > 0`): the sequence is summable;
* `rankDropTailMaj_tail_tendsto_zero` (for `γ > 0`): `A ↦ ∑'_i U(A+i) → 0` as `A → ∞`.

NEW file; depends only on Mathlib.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank-drop tail majorant sequence `C₀·(t+1)·e^{−γt}`. -/
noncomputable def rankDropTailMaj (γ C₀ : ℝ) (t : ℕ) : ℝ :=
  C₀ * ((t : ℝ) + 1) * Real.exp (-γ * (t : ℝ))

/-- Nonnegativity of the tail majorant (given `0 ≤ C₀`). -/
lemma rankDropTailMaj_nonneg {γ C₀ : ℝ} (hC₀ : 0 ≤ C₀) (t : ℕ) :
    0 ≤ rankDropTailMaj γ C₀ t := by
  unfold rankDropTailMaj
  have h1 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp (-γ * (t : ℝ)) := (Real.exp_pos _).le
  positivity

/-- `e^{−γt} = (e^{−γ})^t`, the geometric form used for summability. -/
lemma rankDropTailMaj_exp_pow (γ : ℝ) (t : ℕ) :
    Real.exp (-γ * (t : ℝ)) = (Real.exp (-γ)) ^ t := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- For `γ > 0`, the tail majorant is summable: `(t+1)·r^t` with `r = e^{−γ} ∈ (0,1)`. -/
lemma rankDropTailMaj_summable {γ C₀ : ℝ} (hγ : 0 < γ) :
    Summable (fun t : ℕ => rankDropTailMaj γ C₀ t) := by
  set r : ℝ := Real.exp (-γ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]
    calc Real.exp (-γ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  -- ∑ (t+1)·r^t = ∑ t·r^t + ∑ r^t, both summable
  have hpow1 : Summable (fun t : ℕ => (t : ℝ) ^ 1 * r ^ t) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow0 : Summable (fun t : ℕ => (t : ℝ) ^ 0 * r ^ t) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hnorm
  have hsum : Summable (fun t : ℕ => ((t : ℝ) + 1) * r ^ t) := by
    have := hpow1.add hpow0
    apply this.congr
    intro t
    simp only [pow_one, pow_zero, one_mul]
    ring
  have hC : Summable (fun t : ℕ => C₀ * (((t : ℝ) + 1) * r ^ t)) := hsum.mul_left C₀
  apply hC.congr
  intro t
  unfold rankDropTailMaj
  rw [rankDropTailMaj_exp_pow, ← hr]
  ring

/-- The shifted tail `A ↦ ∑'_i U(A+i)` of a summable nonnegative sequence vanishes as `A → ∞`. -/
lemma rankDropTailMaj_tail_tendsto_zero {γ C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hγ : 0 < γ) :
    Tendsto (fun A : ℕ => ∑' i : ℕ, rankDropTailMaj γ C₀ (A + i)) atTop (𝓝 0) := by
  set U : ℕ → ℝ := fun t => rankDropTailMaj γ C₀ t with hU
  have hsum : Summable U := rankDropTailMaj_summable hγ
  have hUnn : ∀ t, 0 ≤ U t := fun t => rankDropTailMaj_nonneg hC₀ t
  -- ∑'_i U(A+i) = ∑' U − ∑_{range A} U, the partial-sum tail, which → 0.
  have htot : Tendsto (fun A : ℕ => ∑ n ∈ Finset.range A, U n) atTop (𝓝 (∑' n, U n)) :=
    hsum.tendsto_sum_tsum_nat
  have heq : ∀ A : ℕ, (∑' i : ℕ, U (A + i)) = (∑' n, U n) - ∑ n ∈ Finset.range A, U n := by
    intro A
    have hadd := Summable.sum_add_tsum_nat_add A hsum
    -- hadd : (∑ i ∈ range A, U i) + ∑' i, U (i + A) = ∑' i, U i
    have hcomm : (∑' i : ℕ, U (A + i)) = ∑' i : ℕ, U (i + A) := by
      apply tsum_congr; intro i; rw [add_comm]
    rw [hcomm]; linarith [hadd]
  rw [show (0 : ℝ) = (∑' n, U n) - (∑' n, U n) by ring]
  apply (Tendsto.sub tendsto_const_nhds htot).congr
  intro A; rw [heq A]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Ceiling-escape bricks 2 & 3: deep one-step mass ≤ tail majorant, and drop-1 minorization off-band

Two `∀ᶠ v` facts wiring the banked analytics into the abstract super-solution form needed by the
escape brick:

* `oneStep_deep_mass_le_rankDropTail`: for every off-band predecessor `v` (rank `≥ R + A`), the
  one-step *deep-crossing* mass `∑_{k ∈ ceilBand R A, rnk k < R} Pker v k` is `≤ rankDropTailMaj γ C₀
  (g + A)`, `g = rnk v − (R + A)`.  A deep landing `k` has rank drop `> g + A`, so the deep mass is
  bounded by the rank-drop tail beyond `g + A`, hence by the banked tail majorant.

* `rankDrop_one_mass_offBand_ge`: the drop-1 mass `∑_{k < v, rnk v − rnk k = 1} Pker v k = rankDropKer
  v 1 ≥ η` for every off-band `v`, directly from `Pker_rankDrop_minorization`.

NEW file; imports the banked bricks (tail majorant, minorization, kernel) and does not modify them.
Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 2 — deep one-step mass ≤ rank-drop tail majorant (eventual in `v`).**

There are `γ > 0`, `C₀ ≥ 0` such that, eventually in `v`, for every floor `R` and band width `A` with
`R + A ≤ rnk v`, the deep one-step crossing mass (mass landing in `ceilBand R A` strictly below rank
`R`) is bounded by `rankDropTailMaj γ C₀ (g + A)`, where `g = rnk v − (R + A)`.

A deep landing `k` (rank `< R`, so `rnk v − rnk k > rnk v − R = g + A`) is a rank drop `> g + A`; so
the deep mass is `≤` the rank-drop tail beyond `g + A`, hence `≤` the banked majorant. -/
theorem oneStep_deep_mass_le_rankDropTail :
    ∃ (γ C₀ : ℝ), 0 < γ ∧ 0 ≤ C₀ ∧ ∀ᶠ v : ℕ in atTop, ∀ R A : ℕ,
        R + A ≤ rnk v →
        (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), Pker v k)
          ≤ rankDropTailMaj γ C₀ ((rnk v - (R + A)) + A) := by
  classical
  obtain ⟨γ, C₀, hγ, htail⟩ := Pker_rankDrop_tail_majorant
  -- bump C₀ to be nonnegative without weakening the bound (max C₀ 0)
  set C₀' : ℝ := max C₀ 0 with hC₀'def
  have hC₀'nn : 0 ≤ C₀' := le_max_right _ _
  have hC₀le : C₀ ≤ C₀' := le_max_left _ _
  refine ⟨γ, C₀', hγ, hC₀'nn, ?_⟩
  filter_upwards [htail, eventually_ge_atTop 100] with v htailv hv100
  intro R A hRAle
  set g : ℕ := rnk v - (R + A) with hgdef
  -- the deep mass is a sub-sum of Pker v · over predecessors with rank-drop > g + A
  have hsub :
      (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), Pker v k)
        ≤ ∑ k ∈ (Finset.range v).filter
              (fun k => (g + A) < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · -- deep ⊆ {drop > g+A ∧ drop < v}, as subsets of range v
      intro k hk
      rw [Finset.mem_filter, mem_ceilBand_iff] at hk
      obtain ⟨hkband, hkdeep⟩ := hk
      rw [not_le] at hkdeep
      -- k < v: rnk k < R ≤ R + A ≤ rnk v, and rnk strictly mono enough? use rnk_mono contrapositive
      have hkltv : k < v := by
        by_contra h
        push_neg at h
        have : rnk v ≤ rnk k := rnk_mono h
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hkltv, ?_, ?_⟩
      · -- drop = rnk v − rnk k > g + A
        have hrnkv : rnk v = R + A + g := by omega
        have hkle : rnk k ≤ rnk v := rnk_mono hkltv.le
        omega
      · -- drop < v: rnk v − rnk k ≤ rnk v < v? not always; use drop ≤ rnk v and rnk v < v eventually.
        have hkle : rnk k ≤ rnk v := rnk_mono hkltv.le
        -- rnk v − rnk k ≤ rnk v ≤ 3√v < v for v ≥ 10; but to be safe bound by < v via k ≥ 1? Instead:
        -- the drop is < v because rnk v − rnk k ≤ rnk v and rnk v < v for v large; we have v large.
        have hrnkv_lt : rnk v < v := by
          -- rnk v = ⌊3√v⌋ ≤ 3√v < v for v ≥ 100
          have hbd := (rnk_sqrt_bounds v).1
          have hvR : (100 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv100
          have hvpos : (0 : ℝ) < (v : ℝ) := by linarith
          have hsv : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
            Real.mul_self_sqrt hvpos.le
          have hsvpos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
          have hsvge : (10 : ℝ) ≤ Real.sqrt (v : ℝ) := by
            nlinarith [hsv, hsvpos, hvR]
          have h3sv : 3 * Real.sqrt (v : ℝ) < (v : ℝ) := by nlinarith [hsv, hsvge, hsvpos]
          have : (rnk v : ℝ) < (v : ℝ) := by linarith
          exact_mod_cast this
        omega
    · intro k _ _; exact Pker_nonneg v k
  -- regroup that sub-sum as the rank-drop tail beyond g+A, then bound by the majorant
  have hmasseq :
      (∑ k ∈ (Finset.range v).filter
            (fun k => (g + A) < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k)
        = ∑ d ∈ (Finset.range v).filter ((g + A) < ·), rankDropKer v d :=
    (rankDropKer_tail_eq_mass v (g + A)).symm
  rw [hmasseq] at hsub
  refine le_trans hsub ?_
  refine le_trans (htailv (g + A)) ?_
  -- C₀·(g+A+1)·e^{−γ(g+A)} ≤ C₀'·(g+A+1)·e^{−γ(g+A)} = rankDropTailMaj γ C₀' (g+A)
  unfold rankDropTailMaj
  have hb : (0 : ℝ) ≤ ((g + A : ℕ) : ℝ) + 1 := by positivity
  have he : (0 : ℝ) ≤ Real.exp (-γ * ((g + A : ℕ) : ℝ)) := (Real.exp_pos _).le
  have hbe : (0 : ℝ) ≤ (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ)) :=
    mul_nonneg hb he
  calc C₀ * (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))
      = C₀ * ((((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))) := by ring
    _ ≤ C₀' * ((((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₀le hbe
    _ = C₀' * (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ)) := by ring

/-- **Brick 3 — drop-1 minorization off-band.**  There is `η > 0` so that, eventually in `v`, the
drop-1 mass `rankDropKer v 1 ≥ η`.  Direct use of `Pker_rankDrop_minorization` (drop-1 half). -/
theorem rankDrop_one_mass_offBand_ge :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ v : ℕ in atTop, η ≤ rankDropKer v 1 := by
  obtain ⟨η, hη, hminor⟩ := Pker_rankDrop_minorization
  refine ⟨η, hη, ?_⟩
  filter_upwards [hminor] with v hv
  exact hv.1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Ceiling-escape brick 5 (FINAL): `CeilingEscape` ⟹ the unconditional Hardy–Ramanujan limit

This is the last brick of the unconditional partition-ratio limit.  We instantiate the abstract
additive super-solution (`enterBand_deep_mass_le_of_tail_forcing_drop_one`, brick 4) with

* `U = rankDropTailMaj γ C₀` (banked deep-mass tail majorant, brick 2),
* `η` the banked drop-1 minorization (brick 3),
* band width `A = ceilA R`,

and set the escape bound `e R = (1/η)·∑'_i U(ceilA R + i)`.  Then:

* `e R ≥ 0`;
* `e R → 0`, because `ceilA R → ∞` and the shifted tail of `U` vanishes (`rankDropTailMaj_tail_tendsto_zero`);
* the deep first-entrance overshoot from any high start is `≤ e R` (brick 4 at floor `R`, whose
  off-band hypotheses are supplied by the eventual-in-`v` analytics: every off-band `v` has rank
  `≥ R + ceilA R`, hence `v` is large once `R` is large).

This produces `CeilingEscape`, and `erdos_partition_limit_exists_of_escape` concludes the
unconditional `erdos_partition_limit_exists`.

NEW file; imports the banked bricks; does not modify them.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 5 — `CeilingEscape` from the banked analytics.** -/
theorem CeilingEscape_of_rankDropTail_dropOne : CeilingEscape := by
  classical
  -- banked analytics
  obtain ⟨γ, C₀, hγ, hC₀nn, hdeepev⟩ := oneStep_deep_mass_le_rankDropTail
  obtain ⟨η, hη, hdrop1ev⟩ := rankDrop_one_mass_offBand_ge
  set U : ℕ → ℝ := rankDropTailMaj γ C₀ with hUdef
  -- abstract U-facts (so the elaborator never unfolds the concrete majorant downstream)
  have hUnn : ∀ t, 0 ≤ U t := fun t => rankDropTailMaj_nonneg hC₀nn t
  have hUsummable : Summable U := rankDropTailMaj_summable hγ
  have hUtail : Tendsto (fun A : ℕ => ∑' i : ℕ, U (A + i)) atTop (𝓝 0) :=
    rankDropTailMaj_tail_tendsto_zero hC₀nn hγ
  clear_value U
  -- the escape bound e R = (1/η)·∑'_i U(ceilA R + i)
  set e : ℕ → ℝ := fun R => (1 / η) * ∑' i : ℕ, U (ceilA R + i) with hedef
  refine ⟨e, ?_, ?_, ?_⟩
  · -- e R ≥ 0
    intro R
    rw [hedef]
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun i => hUnn _)
  · -- e R → 0
    rw [hedef]
    have hcomp : Tendsto (fun R : ℕ => ∑' i : ℕ, U (ceilA R + i)) atTop (𝓝 0) :=
      hUtail.comp ceilA_tendsto
    have := hcomp.const_mul (1 / η)
    simpa using this
  · -- the escape inequality eventually in R
    -- thresholds for the eventual-in-v facts (bricks 2,3) and kernelMass positivity
    obtain ⟨Vd, hVd⟩ := eventually_atTop.1 hdeepev
    obtain ⟨V1, hV1⟩ := eventually_atTop.1 hdrop1ev
    obtain ⟨Vk, hVk⟩ := eventually_atTop.1 kernelMass_pos_eventually
    set N := max (max Vd V1) (max Vk 2) with hNdef
    -- pick R so that R + ceilA R ≥ 3N+3 (then off-band v ⟹ v ≥ N)
    filter_upwards [eventually_ge_atTop (3 * N + 3)] with R hR
    intro n n' hn hn'
    -- abbreviations
    set A := ceilA R with hAdef
    set B := ceilBand R A with hBdef
    -- conversion: off-band v ⟹ v ≥ N (uses rnk v ≥ R + A ≥ 3N+3)
    have hvbig : ∀ v, v ∉ B → N ≤ v := by
      intro v hv
      have hrkge : R + A ≤ rnk v := not_mem_ceilBand_rank_ge hv
      have : 3 * N + 3 ≤ rnk v := le_trans (by omega) hrkge
      exact rnk_ge_of this
    -- brick-4 hypotheses, universally over off-band v
    have hPnn : ∀ a b, 0 ≤ Pker a b := Pker_nonneg
    have hPsupp : ∀ a b, a ≤ b → Pker a b = 0 := Pker_supp
    have hrow : ∀ v, v ∉ B → ∑ k ∈ Finset.range v, Pker v k = 1 := by
      intro v hv
      have hvN := hvbig v hv
      have hv2 : 2 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvN
      have hvk : Vk ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvN
      exact Pker_mass hv2 (ne_of_gt (hVk v hvk))
    have hdeep : ∀ v, v ∉ B →
        (∑ k ∈ B.filter (fun k => ¬ R ≤ rnk k), Pker v k) ≤ U (A + (rnk v - (R + A))) := by
      intro v hv
      have hvN := hvbig v hv
      have hvd : Vd ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hvN
      have hrkge : R + A ≤ rnk v := not_mem_ceilBand_rank_ge hv
      have h := hVd v hvd R A hrkge
      rwa [add_comm (rnk v - (R + A)) A] at h
    have hdrop1 : ∀ v, v ∉ B →
        η ≤ ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = 1), Pker v k := by
      intro v hv
      have hvN := hvbig v hv
      have hv1 : V1 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hvN
      -- rankDropKer v 1 = the drop-1 mass by definition
      have hrk := hV1 v hv1
      rw [rankDropKer] at hrk
      exact hrk
    -- off-band membership from rank lower bounds
    have hnB : n ∉ B := by
      rw [hBdef]; intro hcon; have := mem_ceilBand_iff.mp hcon; omega
    have hn'B : n' ∉ B := by
      rw [hBdef]; intro hcon; have := mem_ceilBand_iff.mp hcon; omega
    -- apply brick 4 to n and n'
    have hesc_n := enterBand_deep_mass_le_of_tail_forcing_drop_one
      (P := Pker) (R := R) (A := A) (U := U) (η := η)
      hη hUnn hPnn hPsupp hrow hdeep hdrop1 n hnB
    have hesc_n' := enterBand_deep_mass_le_of_tail_forcing_drop_one
      (P := Pker) (R := R) (A := A) (U := U) (η := η)
      hη hUnn hPnn hPsupp hrow hdeep hdrop1 n' hn'B
    -- finite sum ≤ full tsum (1/η factor), giving ≤ e R
    have hsumA : Summable (fun i : ℕ => U (A + i)) := by
      have h := (summable_nat_add_iff A).mpr hUsummable
      apply h.congr; intro i; rw [add_comm]
    have hηinv : (0 : ℝ) ≤ 1 / η := by positivity
    have heR_eq : e R = (1 / η) * ∑' i : ℕ, U (A + i) := by
      rw [hedef, hAdef]
    have hfin_le_e : ∀ m : ℕ,
        (1 / η) * ∑ i ∈ Finset.range (m + 1), U (A + i) ≤ e R := by
      intro m
      rw [heR_eq]
      have hle : ∑ i ∈ Finset.range (m + 1), U (A + i) ≤ ∑' i : ℕ, U (A + i) :=
        hsumA.sum_le_tsum _ (fun i _ => hUnn _)
      exact mul_le_mul_of_nonneg_left hle hηinv
    have hgoal1 : ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer Pker B n z ≤ e R := by
      rw [hBdef]; exact le_trans hesc_n (hfin_le_e _)
    have hgoal2 : ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer Pker B n' z ≤ e R := by
      rw [hBdef]; exact le_trans hesc_n' (hfin_le_e _)
    exact ⟨hgoal1, hgoal2⟩

/-- **The unconditional Hardy–Ramanujan partition limit.**  The normalized partition sequence
`u n = n · p(n) · exp(-C·√n)`, `C = π√(2/3)`, `p n = card (Nat.Partition n)` (the repo's `u`, see
`ErdosKernel.lean`), converges to a positive limit.  Fully unconditional:
`CeilingEscape` is now banked clean-3 via the elementary additive escape route (R9), so the only
inputs are the banked rank-drop tail majorant and drop-1 minorization. -/
theorem erdos_partition_limit_exists :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) :=
  erdos_partition_limit_exists_of_escape CeilingEscape_of_rankDropTail_dropOne

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# The complete Hardy–Ramanujan partition limit (with the exact constant)

`Erdos.erdos_partition_limit_exists` (CeilingEscapeClose) proves the normalized partition sequence
`u n = n · p(n) · exp(−C√n)` (`C = π√(2/3)`) converges to *some* positive limit.
`erdos_limit_constant_of_renewal` (ErdosRiemannError) forces that limit to equal `1/(4√3)`,
unconditionally (the mesh-1 Riemann error is negligible, `riemannError_negligible`).

This file assembles the two into the full Hardy–Ramanujan statement
`u n → 1/(4√3)`, the leading-order partition asymptotic `p(n) ~ exp(π√(2n/3)) / (4n√3)`.
-/

noncomputable section

open Filter Topology

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions
open Filter Topology
theorem solution :
    Tendsto Erdos.u atTop (𝓝 (1 / (4 * Real.sqrt 3))) := by
  obtain ⟨a, ha, hlim⟩ := Erdos.erdos_partition_limit_exists
  rwa [erdos_limit_constant_of_renewal ha hlim] at hlim
