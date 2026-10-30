-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_walls_multiB
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:59:18.24351+00:00
-- url     : https://prove2.me/submissions/01715afc-f330-4ae3-a742-2cf20c060672

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosRenewalConnectMultiB
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_hit
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Mathlib

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
# R7 Fact B via Doeblin (killed kernel): boundary-absorbing kernel powers

The killed kernel `P̃` (predecessor steps above the cutoff, identity-absorb on the boundary) has
support `k ≤ n` (predecessor OR diagonal), so its composition sums over `range (n+1)`.  This file
builds `KCompK`/`KPowK` and proves nonnegativity and the support `n < k → · = 0`.  The `L`-fold killed
power is the law used in the Doeblin pairwise contraction for the exactly-harmonic `hitVal`.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma KCompK_nonneg {P Q : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) (hQ : ∀ n k, 0 ≤ Q n k)
    (n k : ℕ) : 0 ≤ KCompK P Q n k :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hP n j) (hQ j k))

/-- Composition kills `n < k` when the right kernel has support `· ≤ ·` (`a < b → Q a b = 0`). -/
lemma KCompK_support {P Q : ℕ → ℕ → ℝ} (hQ : ∀ a b, a < b → Q a b = 0)
    {n k : ℕ} (hnk : n < k) : KCompK P Q n k = 0 := by
  rw [KCompK]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hQ j k (by omega), mul_zero]

lemma KPowK_nonneg {P : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) :
    ∀ (L n k : ℕ), 0 ≤ KPowK L P n k := by
  intro L
  induction L with
  | zero => intro n k; simp only [KPowK]; split <;> norm_num
  | succ L ih => intro n k; rw [KPowK]; exact KCompK_nonneg hP ih n k

/-- `KPowK L P` has support `n < k → · = 0` (the killed chain never moves to a strictly larger index). -/
lemma KPowK_support {P : ℕ → ℕ → ℝ} : ∀ (L : ℕ) {n k : ℕ}, n < k → KPowK L P n k = 0 := by
  intro L
  induction L with
  | zero => intro n k hnk; simp only [KPowK]; rw [if_neg (by omega)]
  | succ L ih => intro n k hnk; rw [KPowK]; exact KCompK_support (fun a b hab => ih hab) hnk

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the `P̃^L`-harmonic identity

A function `h` that is harmonic above a cutoff (`h n = ∑_{k<n} P n k · h k` for `rank n ≥ J`, and
`h n = φ n` below) is exactly harmonic for the *killed* kernel `P̃` summed over `range (n+1)`, and hence
for every power `KPowK L P̃`:  `h n = ∑_{k ∈ range (n+1)} (KPowK L P̃) n k · h k`.  Proof by induction on
`L` (one-step + `Finset.sum_comm` + support truncation).  This is the exact-harmonicity (η = 0) that
makes the Doeblin oscillation contraction error-free for `hitVal`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ} {h φ : ℕ → ℝ}

/-- One-step killed harmonicity (over `range (n+1)`). -/
lemma killed_harmonic_one (hPsupp : ∀ n k, n ≤ k → P n k = 0)
    (heq : ∀ n, h n = if rank n < J then φ n else ∑ k ∈ Finset.range n, P n k * h k) (n : ℕ) :
    h n = ∑ k ∈ Finset.range (n + 1), killedKer P rank J n k * h k := by
  unfold killedKer
  by_cases hb : rank n < J
  · simp only [if_pos hb, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n h, if_pos (Finset.self_mem_range_succ n)]
  · simp only [if_neg hb]
    rw [Finset.sum_range_succ, hPsupp n n (le_refl n), zero_mul, add_zero, heq n, if_neg hb]

/-- `h` is harmonic for every killed power `KPowK L P̃` (summed over `range (n+1)`). -/
lemma killed_harmonic_pow (hPsupp : ∀ n k, n ≤ k → P n k = 0)
    (heq : ∀ n, h n = if rank n < J then φ n else ∑ k ∈ Finset.range n, P n k * h k) :
    ∀ (L n : ℕ), h n = ∑ k ∈ Finset.range (n + 1), KPowK L (killedKer P rank J) n k * h k := by
  intro L
  induction L with
  | zero =>
    intro n
    simp only [KPowK, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n h, if_pos (Finset.self_mem_range_succ n)]
  | succ L ih =>
    intro n
    have key : ∑ k ∈ Finset.range (n + 1), KPowK (L + 1) (killedKer P rank J) n k * h k
        = ∑ j ∈ Finset.range (n + 1), killedKer P rank J n j * h j := by
      simp only [KPowK, KCompK]
      rw [Finset.sum_congr rfl (fun k _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      -- ∑_{k ∈ range (n+1)} (KPowK L P̃) j k * h k = h j
      have htrunc : ∑ k ∈ Finset.range (n + 1), KPowK L (killedKer P rank J) j k * h k
          = ∑ k ∈ Finset.range (j + 1), KPowK L (killedKer P rank J) j k * h k := by
        have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          exact lt_of_lt_of_le hx (Nat.succ_le_succ (Nat.lt_succ_iff.mp hj))
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hks
        rw [Finset.mem_range] at hks
        have hjk : j < k := Nat.not_lt.mp hks
        rw [KPowK_support L hjk, zero_mul]
      rw [htrunc, ← ih j]
    rw [key, ← killed_harmonic_one hPsupp heq n]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the killed kernel and its powers are row-stochastic

To feed `KPowK L P̃` into the Doeblin escape contraction (`doeblin_average_diff_bound` /
`doeblin_escape_bound`, whose `p, q` must be probability vectors), we need each row of `P̃` and of every
power `KPowK L P̃` to sum to `1` over `range (n+1)`.  Given the base kernel `P` is row-stochastic over
`range n` (the predecessor mass is normalized) with predecessor support (`n ≤ k → P n k = 0`), the
killed kernel absorbs the missing diagonal mass below the cutoff, so `∑_{k ∈ range (n+1)} P̃ n k = 1`;
the powers then preserve this by induction (the inner row-sum truncates to `range (j+1)` via
`KPowK_support`).  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ}

/-- The killed kernel is row-stochastic over `range (n+1)`.  The base kernel `P` need only be
row-stochastic on the active branch `rank n ≥ J`; below the cutoff the kernel absorbs (mass `1`). -/
lemma killedKer_row_sum (hrow : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k = 1)
    (hsupp : ∀ n k, n ≤ k → P n k = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), killedKer P rank J n k = 1 := by
  unfold killedKer
  by_cases hb : rank n < J
  · simp only [if_pos hb]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun _ => (1 : ℝ)),
      if_pos (Finset.self_mem_range_succ n)]
  · simp only [if_neg hb]
    rw [Finset.sum_range_succ, hsupp n n (le_refl n), add_zero, hrow n (not_lt.mp hb)]

/-- Every killed power is row-stochastic over `range (n+1)`. -/
lemma KPowK_row_sum {Q : ℕ → ℕ → ℝ}
    (hQrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Q m k = 1) :
    ∀ (L n : ℕ), ∑ k ∈ Finset.range (n + 1), KPowK L Q n k = 1 := by
  intro L
  induction L with
  | zero =>
    intro n
    simp only [KPowK]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun _ => (1 : ℝ)),
      if_pos (Finset.self_mem_range_succ n)]
  | succ L ih =>
    intro n
    simp only [KPowK, KCompK]
    -- ∑_k ∑_j Q n j · (KPowK L Q) j k  =  ∑_j Q n j · ∑_k (KPowK L Q) j k
    rw [Finset.sum_comm]
    have : ∀ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1), Q n j * KPowK L Q j k = Q n j := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← Finset.mul_sum]
      -- truncate the inner sum from range (n+1) to range (j+1)
      have htrunc : ∑ k ∈ Finset.range (n + 1), KPowK L Q j k
          = ∑ k ∈ Finset.range (j + 1), KPowK L Q j k := by
        have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          exact lt_of_lt_of_le hx (Nat.succ_le_succ (Nat.lt_succ_iff.mp hj))
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hks
        rw [Finset.mem_range] at hks
        exact KPowK_support L (Nat.not_lt.mp hks)
      rw [htrunc, ih j, mul_one]
    rw [Finset.sum_congr rfl this, hQrow n]

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

/-- The killed Erdős kernel is nonnegative. -/
lemma killedKer_Pker_nonneg (J n k : ℕ) : 0 ≤ killedKer Pker rnk J n k := by
  unfold killedKer
  by_cases h : rnk n < J
  · simp only [if_pos h]; split <;> norm_num
  · simp only [if_neg h]; exact Pker_nonneg n k

/-- `Pker` is supported on strict predecessors (`n ≤ k → Pker n k = 0`). -/
lemma Pker_supp (n k : ℕ) (h : n ≤ k) : Pker n k = 0 := by
  unfold Pker; rw [if_neg (by omega)]

/-- For `J` large enough, `rnk n ≥ J` forces `n` into the region where `Pker` is row-stochastic. -/
lemma Pker_rowsum_rank {N₀ : ℕ} (hN₀2 : 2 ≤ N₀) (hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0)
    {J : ℕ} (hJ : 3 * N₀ + 3 ≤ J) {n : ℕ} (hn : J ≤ rnk n) :
    ∑ k ∈ Finset.range n, Pker n k = 1 := by
  have hge : N₀ ≤ n := rnk_ge_of (le_trans hJ hn)
  exact Pker_mass (by omega) (hkm n hge)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the multi-scale step contraction (constant forcing)

The escape-split engine `tendsto_zero_of_step_contraction` needs the forcing `e(R) → 0`.  For the Erdős
kernel the escape mass below a *fixed* band `{rnk ≥ R−B}` is `~ e^{−cB}`, a CONSTANT in `R` (a normalized
tail), so that engine cannot apply with fixed `B`.  The fix is multi-scale: for each band width `B` the
contraction `W(n+L) ≤ q·W n + c` (constant `c = c(B)`) gives only `limsup W ≤ c/(1−q)`, but letting
`B → ∞` drives the bound to `0`.  This file provides the two engine pieces:

* `limsup_le_of_step_contraction_const` — bounded forcing ⟹ bounded `limsup`;
* `tendsto_zero_of_limsup_le_all` — a `limsup` dominated by a null sequence of bounds ⟹ `→ 0`.

Together they drive the tail oscillation to `0` from the *family* of band contractions.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `L`-step contraction with a CONSTANT forcing bounds the `limsup`: `W(n+L) ≤ q·W n + c` ⟹
`limsup W ≤ c/(1−q)`. -/
theorem limsup_le_of_step_contraction_const {W : ℕ → ℝ} {q c : ℝ} {L : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hWnn : ∀ n, 0 ≤ W n) (hWbd : BddAbove (Set.range W))
    (hrec : ∀ᶠ n in atTop, W (n + L) ≤ q * W n + c) :
    limsup W atTop ≤ c / (1 - q) := by
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  have hbddU : IsBoundedUnder (· ≤ ·) atTop W := hWbd.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop W := hBB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop W := hbddL.isCoboundedUnder_le
  set Λ := limsup W atTop with hΛ
  have hkey : ∀ ε : ℝ, 0 < ε → Λ ≤ q * (Λ + ε) + c := by
    intro ε hε
    have hWev : ∀ᶠ n in atTop, W n < Λ + ε :=
      eventually_lt_of_limsup_lt (by simp only [hΛ]; linarith) hbddU
    have hcomb : ∀ᶠ n in atTop, W (n + L) ≤ q * (Λ + ε) + c := by
      filter_upwards [hrec, hWev] with n hr hw
      have h1 : q * W n ≤ q * (Λ + ε) := mul_le_mul_of_nonneg_left hw.le hq0
      linarith
    have hshift : ∀ᶠ m in atTop, W m ≤ q * (Λ + ε) + c := by
      obtain ⟨N, hN⟩ := eventually_atTop.1 hcomb
      filter_upwards [eventually_ge_atTop (N + L)] with m hm
      have hmL : L ≤ m := by omega
      have := hN (m - L) (by omega)
      rwa [Nat.sub_add_cancel hmL] at this
    exact limsup_le_of_le hcobddU hshift
  have hΛq : Λ ≤ q * Λ + c := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hk := hkey (δ / (q + 1)) (by positivity)
    have hcc : (q + 1) * (δ / (q + 1)) = δ := by field_simp
    nlinarith [hk, hcc]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - q)]
  nlinarith [hΛq]

/-- A `limsup` bounded by every term of a null sequence is `0`, so a nonnegative bounded sequence with
this property converges to `0`. -/
theorem tendsto_zero_of_limsup_le_all {W B : ℕ → ℝ}
    (hWnn : ∀ n, 0 ≤ W n) (hWbd : BddAbove (Set.range W))
    (hlimsup : ∀ k : ℕ, limsup W atTop ≤ B k)
    (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto W atTop (𝓝 0) := by
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  have hbddU : IsBoundedUnder (· ≤ ·) atTop W := hWbd.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop W := hBB.isBoundedUnder_of_range
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop W := hbddU.isCoboundedUnder_ge
  have hΛnn : 0 ≤ limsup W atTop := le_limsup_of_frequently_le (Frequently.of_forall hWnn) hbddU
  have hle : limsup W atTop ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hB (Eventually.of_forall hlimsup)
  have hL0 : limsup W atTop = 0 := le_antisymm hle hΛnn
  have hliminf_nn : 0 ≤ liminf W atTop :=
    le_liminf_of_le hcobddL (Eventually.of_forall hWnn)
  have hliminf_le : liminf W atTop ≤ limsup W atTop := liminf_le_limsup hbddU hbddL
  have hl0 : liminf W atTop = 0 := le_antisymm (by rw [← hL0]; exact hliminf_le) hliminf_nn
  exact tendsto_of_liminf_eq_limsup hl0 hL0 hbddU hbddL

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the multi-scale §9 assembly (correct for the Erdős kernel)

The escape-split capstone `tendsto_of_killed_doeblin` needs escape mass `→ 0` at a *fixed* band width,
which the Erdős kernel does not satisfy (the escape below a fixed band is `~ e^{−cB}`, constant in `R`).
The correct assembly is multi-scale: for each band width `B` the tail oscillation obeys
`V(R) ≤ (1−δ_B)·V(R−B) + δ_B·bnd B` (`R ≥ R₀(B)`), giving `limsup V ≤ bnd B`; letting `bnd B → 0`
forces `V → 0`, hence `h` converges.  The per-`B` contraction is produced exactly as in
`tendsto_of_killed_doeblin` (overlap `δ_B` on band `B` + escape, via `doeblin_escape_bound`), with
`bnd B = 3·ε_B·M / δ_B`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Multi-scale tail-oscillation engine.** A family of band contractions whose `limsup` bounds vanish
forces `h` to converge. -/
theorem tendsto_of_tailOsc_multiB {h : ℕ → ℝ} {rank : ℕ → ℕ} {M : ℝ} {bnd : ℕ → ℝ}
    (hM : ∀ n, |h n| ≤ M) (hrank : Tendsto rank atTop atTop)
    (hbnd0 : ∀ B, 0 ≤ bnd B) (hbnd : Tendsto bnd atTop (𝓝 0))
    (hcontract : ∀ B : ℕ, ∃ (δ : ℝ) (R₀ : ℕ), 0 < δ ∧ δ ≤ 1 ∧
        ∀ R, R₀ ≤ R → tailOsc h rank R ≤ (1 - δ) * tailOsc h rank (R - B) + δ * bnd B) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  have hWnn : ∀ R, 0 ≤ tailOsc h rank R := fun R => tailOsc_nonneg hrank hM R
  have hWbd : BddAbove (Set.range (fun R => tailOsc h rank R)) :=
    ⟨2 * M, by rintro _ ⟨n, rfl⟩; exact tailOsc_le_two_M hrank hM n⟩
  have hVtend : Tendsto (fun R => tailOsc h rank R) atTop (𝓝 0) := by
    refine tendsto_zero_of_limsup_le_all hWnn hWbd (fun B => ?_) hbnd
    obtain ⟨δ, R₀, hδ0, hδ1, hcon⟩ := hcontract B
    have hrec : ∀ᶠ R in atTop,
        tailOsc h rank (R + B) ≤ (1 - δ) * tailOsc h rank R + δ * bnd B := by
      filter_upwards [eventually_ge_atTop R₀] with R hR
      have hc := hcon (R + B) (le_trans hR (Nat.le_add_right R B))
      rwa [Nat.add_sub_cancel] at hc
    have hls := limsup_le_of_step_contraction_const (W := fun R => tailOsc h rank R)
      (q := 1 - δ) (c := δ * bnd B) (L := B) (by linarith) (by linarith)
      hWnn hWbd hrec
    calc limsup (fun R => tailOsc h rank R) atTop
        ≤ δ * bnd B / (1 - (1 - δ)) := hls
      _ = bnd B := by
          rw [show (1 : ℝ) - (1 - δ) = δ by ring]; field_simp
  exact tendsto_of_tail_osc_to_zero hrank hVtend (fun R i j hi hj => tailOsc_abs_le hM hi hj)

/-- **Multi-scale killed-Doeblin convergence.** A bounded `KPowK L_B P̃`-harmonic `h` converges given,
for each band width `B`, a finite-time overlap `δ_B > 0` on the band `{rnk ≥ R−B}` and escape mass
`≤ ε_B` below it, with `3·ε_B·M / δ_B → 0`. -/
theorem tendsto_of_killed_doeblin_multiB {h : ℕ → ℝ} {rank : ℕ → ℕ} {Pt : ℕ → ℕ → ℝ}
    {M : ℝ} {bnd : ℕ → ℝ}
    (hM : ∀ n, |h n| ≤ M)
    (hrank : Tendsto rank atTop atTop)
    (hPtnn : ∀ n k, 0 ≤ Pt n k)
    (hPtrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Pt m k = 1)
    (hbnd0 : ∀ B, 0 ≤ bnd B) (hbnd : Tendsto bnd atTop (𝓝 0))
    (hwalls : ∀ B : ℕ, ∃ (δ : ℝ) (R₀ L : ℕ),
        0 < δ ∧ δ ≤ 1 ∧
        (∀ n, h n = ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k * h k) ∧
        (∀ R, R₀ ≤ R → ∀ i j, R ≤ rank i → R ≤ rank j →
           δ ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rank k),
                  min (KPowK L Pt i k) (KPowK L Pt j k)) ∧
        (∀ R, R₀ ≤ R → ∀ i, R ≤ rank i →
           ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)),
                  KPowK L Pt i k ≤ δ * bnd B / (3 * M + 1))) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (h 0)) (hM 0)
  refine tendsto_of_tailOsc_multiB hM hrank hbnd0 hbnd (fun B => ?_)
  obtain ⟨δ, R₀, L, hδ0, hδ1, hharm, hoverlap, hescape⟩ := hwalls B
  have hPpownn : ∀ n k, 0 ≤ KPowK L Pt n k := KPowK_nonneg hPtnn L
  have hPprow : ∀ n, ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k = 1 := KPowK_row_sum hPtrow L
  have hPpsupp : ∀ a b, a < b → KPowK L Pt a b = 0 := fun a b hab => KPowK_support L hab
  refine ⟨δ, R₀, hδ0, hδ1, fun R hR => ?_⟩
  -- pairwise bound via doeblin_escape_bound, then tailOsc_le_of_pairwise
  refine tailOsc_le_of_pairwise hrank (fun i j hi hj => ?_)
  set s := Finset.range (max i j + 1) with hs
  have hsub_i : Finset.range (i + 1) ⊆ s := by
    rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
    exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_left i j))
  have hsub_j : Finset.range (j + 1) ⊆ s := by
    rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
    exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_right i j))
  have hext_i : h i = ∑ k ∈ s, KPowK L Pt i k * h k := by
    rw [hharm i]; refine Finset.sum_subset hsub_i (fun k _ hk => ?_)
    rw [Finset.mem_range] at hk; rw [hPpsupp i k (Nat.not_lt.mp hk), zero_mul]
  have hext_j : h j = ∑ k ∈ s, KPowK L Pt j k * h k := by
    rw [hharm j]; refine Finset.sum_subset hsub_j (fun k _ hk => ?_)
    rw [Finset.mem_range] at hk; rw [hPpsupp j k (Nat.not_lt.mp hk), zero_mul]
  have hpm_i : ∑ k ∈ s, KPowK L Pt i k = 1 := by
    rw [← hPprow i]; refine (Finset.sum_subset hsub_i (fun k _ hk => ?_)).symm
    rw [Finset.mem_range] at hk; exact hPpsupp i k (Nat.not_lt.mp hk)
  have hpm_j : ∑ k ∈ s, KPowK L Pt j k = 1 := by
    rw [← hPprow j]; refine (Finset.sum_subset hsub_j (fun k _ hk => ?_)).symm
    rw [Finset.mem_range] at hk; exact hPpsupp j k (Nat.not_lt.mp hk)
  -- bad-mass bounds (reduce to escape over range(i+1)) — bounded by δ·bnd B/(3M+1)
  have hbad_i : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k
      ≤ δ * bnd B / (3 * M + 1) := by
    have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k
        = ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_i) (fun k hk hk2 => ?_)).symm
      have hk2' : k ∉ Finset.range (i + 1) := fun hc =>
        hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
      rw [Finset.mem_range] at hk2'; exact hPpsupp i k (Nat.not_lt.mp hk2')
    rw [heq]; exact hescape R hR i hi
  have hbad_j : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k
      ≤ δ * bnd B / (3 * M + 1) := by
    have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k
        = ∑ k ∈ (Finset.range (j + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_j) (fun k hk hk2 => ?_)).symm
      have hk2' : k ∉ Finset.range (j + 1) := fun hc =>
        hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
      rw [Finset.mem_range] at hk2'; exact hPpsupp j k (Nat.not_lt.mp hk2')
    rw [heq]; exact hescape R hR j hj
  have hfband : ∀ k ∈ s.filter (fun k => R - B ≤ rank k),
      tailInf h rank (R - B) ≤ h k ∧ h k ≤ tailInf h rank (R - B) + tailOsc h rank (R - B) := by
    intro k hk
    have hGk : R - B ≤ rank k := (Finset.mem_filter.mp hk).2
    obtain ⟨hb1, hb2⟩ := tail_band hM hGk
    exact ⟨hb1, by rw [tailOsc]; linarith⟩
  set η := δ * bnd B / (3 * M + 1) with hη
  have hη0 : 0 ≤ η := by
    rw [hη]; apply div_nonneg (mul_nonneg hδ0.le (hbnd0 B)); linarith
  have hdoeb := doeblin_escape_bound (s := s) (p := KPowK L Pt i) (q := KPowK L Pt j)
    (f := h) (δ := δ) (η := η) (lo := tailInf h rank (R - B)) (W := tailOsc h rank (R - B))
    (M := M) (fun k => R - B ≤ rank k)
    (fun k _ => hPpownn i k) (fun k _ => hPpownn j k)
    hpm_i hpm_j (hoverlap R hR i j hi hj) hbad_i hbad_j hfband
    (tailOsc_nonneg hrank hM (R - B)) (fun k _ => hM k)
    (tailInf_abs_le hrank hM (R - B)) hη0
  rw [← hext_i, ← hext_j] at hdoeb
  -- |h i − h j| ≤ (1−δ)·V(R−B) + 3·η·M ;  3·η·M ≤ δ·bnd B
  have hP : 0 ≤ δ * bnd B := mul_nonneg hδ0.le (hbnd0 B)
  have hden : (0 : ℝ) < 3 * M + 1 := by linarith
  have h3ηM : 3 * η * M ≤ δ * bnd B := by
    rw [hη, show 3 * (δ * bnd B / (3 * M + 1)) * M = 3 * M * (δ * bnd B) / (3 * M + 1) by ring,
      div_le_iff₀ hden]
    nlinarith [hP, hMnn]
  calc h i - h j ≤ |h i - h j| := le_abs_self _
    _ ≤ (1 - δ) * tailOsc h rank (R - B) + 3 * η * M := hdoeb
    _ ≤ (1 - δ) * tailOsc h rank (R - B) + δ * bnd B := by linarith [h3ηM]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: the multi-scale connection to `erdos_partition_limit_exists`

The correct (multi-scale) Hardy–Ramanujan reduction for the Erdős kernel.  The walls are B-indexed:
for each band width `B` a finite-time overlap `δ_B > 0` on `{rnk ≥ R−B}` and an escape mass `≤ ε_B`
below it, with `ε_B / δ_B → 0`.  (Unlike the fixed-band escape-split version, the escape here need not
vanish at any single `B`; the *family* with `ε_B/δ_B → 0` drives the tail oscillation to `0`.)  This is
the satisfiable form of `DoeblinWalls`.  Opus-authored.
-/

noncomputable section

open Filter Topology

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
theorem solution
    (hwalls : ∀ᶠ J : ℕ in atTop, DoeblinWallsMultiB J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0 := fun n hn =>
    ne_of_gt (hN₁ n (le_trans (le_max_left _ _) hn))
  have hN₀2 : 2 ≤ N₀ := le_max_right _ _
  have h3Mu : (0 : ℝ) < 3 * Mu + 1 := by linarith
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [hwalls, eventually_ge_atTop (3 * N₀ + 3)] with J hWJ hJ
  obtain ⟨δ, ε, L, R₀, hδ0, hδ1, hε0, hεδ, hoverlap, hescape⟩ := hWJ
  set bnd := fun B => (3 * Mu + 1) * (ε B / δ B) with hbnddef
  have hbnd0 : ∀ B, 0 ≤ bnd B := fun B => by
    rw [hbnddef]; exact mul_nonneg h3Mu.le (div_nonneg (hε0 B) (hδ0 B).le)
  have hbnd : Tendsto bnd atTop (𝓝 0) := by
    have := hεδ.const_mul (3 * Mu + 1)
    simpa [hbnddef] using this
  refine tendsto_of_killed_doeblin_multiB (M := Mu) (rank := rnk)
    (Pt := killedKer Pker rnk J) (bnd := bnd)
    (hitVal_abs_le hMu0 hMu Pker_nonneg (fun n _ => Pker_sum_le_one n))
    rnk_tendsto_atTop
    (killedKer_Pker_nonneg J)
    (fun m => killedKer_row_sum (fun n hn => Pker_rowsum_rank hN₀2 hkm hJ hn) Pker_supp m)
    hbnd0 hbnd
    (fun B => ⟨δ B, R₀ B, L B, hδ0 B, hδ1 B,
      (fun n => killed_harmonic_pow Pker_supp (hitVal_eq Pker rnk J u) (L B) n),
      hoverlap B, fun R hR i hi => ?_⟩)
  -- escape ≤ ε B = δ B · bnd B / (3 Mu + 1)
  refine (hescape B R hR i hi).trans (le_of_eq ?_)
  have hδne : δ B ≠ 0 := (hδ0 B).ne'
  have h3ne : (3 * Mu + 1) ≠ 0 := h3Mu.ne'
  simp only [hbnddef]
  field_simp
