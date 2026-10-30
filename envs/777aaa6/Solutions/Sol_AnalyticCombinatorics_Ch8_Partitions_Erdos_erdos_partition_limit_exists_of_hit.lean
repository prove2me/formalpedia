-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_hit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:55:15.18833+00:00
-- url     : https://prove2.me/submissions/9a036a38-a854-4110-88b3-f292a3f52dc8

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions

open scoped BigOperators

lemma part_pos (n : ℕ) : 0 < part n := by
  dsimp [part]
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

end AnalyticCombinatorics.Ch8.Partitions
end

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

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

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

lemma boundaryTerm_nonneg (n : ℕ) : 0 ≤ boundaryTerm n := by
  dsimp [boundaryTerm]
  exact mul_nonneg (sigmaR_nonneg n) (Real.exp_pos _).le

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

/-- Lower barrier `1 + A/log(n+E)`. -/
noncomputable def lowerBarrier (A E : ℝ) (n : ℕ) : ℝ :=
  1 + A / Real.log ((n : ℝ) + E)

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

/-- Lower barrier eventually in `[1, 1 + A]`. -/
lemma lowerBarrier_eventually_pos_bdd {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ lowerBarrier A E n ∧ lowerBarrier A E n ≤ 1 + A := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hgt : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt
  constructor
  · rw [lowerBarrier]
    have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
    linarith
  · rw [lowerBarrier]
    -- log(n+E) ≥ log(1+3) ≥ 1 eventually... uniform: n ≥ 1, E ≥ 3 ⇒ n+E ≥ 4 ⇒ log ≥ log 4 > 1
    have h4 : (4 : ℝ) ≤ (n : ℝ) + E := by linarith
    have hlog4 : (1 : ℝ) ≤ Real.log ((n : ℝ) + E) := by
      have hl4 : Real.log 4 ≤ Real.log ((n : ℝ) + E) :=
        Real.log_le_log (by norm_num) h4
      have : (1 : ℝ) ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have hl2 : 0.6931471803 ≤ Real.log 2 := Real.log_two_gt_d9.le
        push_cast
        nlinarith
      linarith
    have : A / Real.log ((n : ℝ) + E) ≤ A := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
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

/-- `lowerBarrier` is antitone in `n` (for `A > 0`, `E ≥ 3`). -/
lemma lowerBarrier_anti {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    Antitone (lowerBarrier A E) := by
  intro k l hkl
  have hk : (1 : ℝ) < (k : ℝ) + E := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hlogk : 0 < Real.log ((k : ℝ) + E) := Real.log_pos hk
  have hmono : Real.log ((k : ℝ) + E) ≤ Real.log ((l : ℝ) + E) := by
    apply Real.log_le_log (by linarith)
    have : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  rw [lowerBarrier, lowerBarrier]
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

/--
**Lower barrier is subharmonic, conditional on the mass rate** (R6 lemma 6).
-/
theorem lowerBarrier_kernel_subharmonic_of_rate
    {E : ℝ} (hE : 3 ≤ E)
    (hrate : ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ n : ℕ in atTop, |kernelMass n - 1| ≤ ρ * barrierSlack E n) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ n : ℕ in atTop,
        lowerBarrier A E n + δ * barrierSlack E n
          ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m)) := by
  classical
  obtain ⟨a₀, b₀, μ, ha₀, hab₀, hμ, hwinmass⟩ := erdos_kernel_fixed_window_pos
  have hA : (0 : ℝ) < 1 := one_pos
  set A : ℝ := 1 with hAdef
  set c : ℝ := A * a₀ / 2 with hcdef
  have hc : 0 < c := by rw [hcdef, hAdef]; positivity
  -- |H₋| ≤ 1 + A = 2 eventually; absorb with ρ := c·μ/4
  set ρ : ℝ := c * μ / 4 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  refine ⟨A, c * μ / 2, hA, by positivity, ?_⟩
  filter_upwards [barrier_core_gap_on_window hA hE ha₀ hab₀, hwinmass, hrate ρ hρ,
    barrierSlack_eventually_pos hE, lowerBarrier_eventually_pos_bdd hA hE,
    eventually_ge_atTop 1] with n hgap hwin hr hsl hbdd hn1
  have hsplit := kernel_sum_split a₀ b₀ n (lowerBarrier A E)
  -- window piece gains c·slack per unit mass
  have hwin_term : (lowerBarrier A E n + c * barrierSlack E n) * kernelWindow a₀ b₀ n
      ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then erdosWeight n m * lowerBarrier A E (n - m) else 0) := by
    rw [kernelWindow, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
    · rw [if_pos hwinm, if_pos hwinm]
      have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
      have hcore := hgap m hwinm.1 hwinm.2
      have hble : lowerBarrier A E n + c * barrierSlack E n ≤ lowerBarrier A E (n - m) := by
        rw [lowerBarrier, lowerBarrier] at *
        rw [hcdef]
        linarith [hcore]
      calc (lowerBarrier A E n + c * barrierSlack E n) * erdosWeight n m
          = erdosWeight n m * (lowerBarrier A E n + c * barrierSlack E n) := by ring
        _ ≤ erdosWeight n m * lowerBarrier A E (n - m) :=
            mul_le_mul_of_nonneg_left hble hW
    · rw [if_neg hwinm, if_neg hwinm, mul_zero]
  -- off-window piece: H₋(n−m) ≥ H₋(n)
  have hoff_term : lowerBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n)
      ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then 0 else erdosWeight n m * lowerBarrier A E (n - m)) := by
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
      have hanti := lowerBarrier_anti hA hE hmle
      calc lowerBarrier A E n * erdosWeight n m
          = erdosWeight n m * lowerBarrier A E n := by ring
        _ ≤ erdosWeight n m * lowerBarrier A E (n - m) :=
            mul_le_mul_of_nonneg_left hanti hW
  -- assemble
  have htotal : lowerBarrier A E n * kernelMass n + c * barrierSlack E n * kernelWindow a₀ b₀ n
      ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m)) := by
    rw [hsplit]
    have := add_le_add hwin_term hoff_term
    calc lowerBarrier A E n * kernelMass n + c * barrierSlack E n * kernelWindow a₀ b₀ n
        = (lowerBarrier A E n + c * barrierSlack E n) * kernelWindow a₀ b₀ n
          + lowerBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n) := by ring
      _ ≤ _ := this
  -- mass error absorption: H₋·mass ≥ H₋ − 2ρ·slack (|H₋| ≤ 2 eventually since A = 1)
  have hH2 : |lowerBarrier A E n| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith [hbdd.1]
    · rw [hAdef] at hbdd
      linarith [hbdd.2]
  have hmass_abs : lowerBarrier A E n - 2 * (ρ * barrierSlack E n)
      ≤ lowerBarrier A E n * kernelMass n := by
    have h1 : lowerBarrier A E n * kernelMass n
        = lowerBarrier A E n + lowerBarrier A E n * (kernelMass n - 1) := by ring
    rw [h1]
    have h2 : -(2 * (ρ * barrierSlack E n)) ≤ lowerBarrier A E n * (kernelMass n - 1) := by
      have h3 : |lowerBarrier A E n * (kernelMass n - 1)| ≤ 2 * (ρ * barrierSlack E n) := by
        rw [abs_mul]
        apply mul_le_mul hH2 hr (abs_nonneg _) (by norm_num)
      linarith [(abs_le.mp h3).1]
    linarith
  have hwin_lower : c * barrierSlack E n * μ ≤ c * barrierSlack E n * kernelWindow a₀ b₀ n := by
    apply mul_le_mul_of_nonneg_left hwin
    positivity
  -- δ = cμ/2: H₋ + cμ/2·slack ≤ H₋ − 2ρ slack + cμ slack  (since 2ρ = cμ/2)
  calc lowerBarrier A E n + c * μ / 2 * barrierSlack E n
      = (lowerBarrier A E n - 2 * (ρ * barrierSlack E n)) + c * barrierSlack E n * μ := by
        rw [hρdef]
        ring
    _ ≤ lowerBarrier A E n * kernelMass n + c * barrierSlack E n * kernelWindow a₀ b₀ n := by
        linarith [hmass_abs, hwin_lower]
    _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m)) := htotal

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

/-- `u` is positive for `n ≥ 1` (R6 lemma 10). -/
lemma u_pos {n : ℕ} (hn : 1 ≤ n) : 0 < u n := by
  rw [u]
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 := Partitions.part_pos n
  have h3 : (0 : ℝ) < Real.exp (-C * Real.sqrt (n : ℝ)) := Real.exp_pos _
  positivity

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

/--
**Lower bound by barrier induction** (R6 lemma 11): a subharmonic lower barrier
supports `u` from below up to a constant, for all `n ≥ 1`.
-/
theorem u_lower_of_subharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hsub : ∀ᶠ n : ℕ in atTop,
      lowerBarrier A E n + δ * barrierSlack E n
        ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * lowerBarrier A E n ≤ u n := by
  classical
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsub
  set N₀ : ℕ := max N₁ 2 with hN₀def
  -- c below the initial segment ratios; H₋ ∈ [1, 1+A] always (E ≥ 3)
  have hH_ge_one : ∀ k : ℕ, 1 ≤ lowerBarrier A E k := by
    intro k
    rw [lowerBarrier]
    have h1 : (1 : ℝ) < (k : ℝ) + E := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hlog : 0 < Real.log ((k : ℝ) + E) := Real.log_pos h1
    have : 0 ≤ A / Real.log ((k : ℝ) + E) := by positivity
    linarith
  have hH_pos : ∀ k : ℕ, 0 < lowerBarrier A E k := fun k =>
    lt_of_lt_of_le one_pos (hH_ge_one k)
  -- min of u k / H₋ k over 1 ≤ k ≤ N₀, capped by 1... use inf'
  have hne : ((Finset.Icc 1 N₀)).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, ?_⟩⟩
    omega
  set c₀ : ℝ := (Finset.Icc 1 N₀).inf' hne (fun k => u k / lowerBarrier A E k) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    apply Finset.lt_inf'_iff hne (a := (0:ℝ)) |>.mpr
    intro k hk
    obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
    exact div_pos (u_pos hk1) (hH_pos k)
  set c : ℝ := min c₀ 1 with hcdef
  have hcpos : 0 < c := lt_min hc₀pos one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  refine ⟨c, hcpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hsmall : n ≤ N₀
    · -- initial segment
      have hmem : n ∈ Finset.Icc 1 N₀ := Finset.mem_Icc.mpr ⟨hn1, hsmall⟩
      have hinf : c₀ ≤ u n / lowerBarrier A E n :=
        Finset.inf'_le (fun k => u k / lowerBarrier A E k) hmem
      have hcle : c ≤ u n / lowerBarrier A E n := le_trans (min_le_left _ _) hinf
      have hHpos := hH_pos n
      calc c * lowerBarrier A E n
          ≤ (u n / lowerBarrier A E n) * lowerBarrier A E n :=
            mul_le_mul_of_nonneg_right hcle hHpos.le
        _ = u n := by field_simp
    · push_neg at hsmall
      have hn2 : 2 ≤ n := by omega
      have hnN₁ : N₁ ≤ n := by omega
      have hrec := u_recurrence n hn2
      have hsub_n := hN₁ n hnN₁
      -- termwise IH (all n−m ∈ [1, n−1])
      have hterm : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (c * lowerBarrier A E (n - m)))
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hlt : n - m < n := by omega
        have hge1 : 1 ≤ n - m := by omega
        exact mul_le_mul_of_nonneg_left (ih (n - m) hlt hge1) hW
      have hfactor : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (c * lowerBarrier A E (n - m)))
          = c * ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * lowerBarrier A E (n - m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        ring
      have hbdy : 0 ≤ boundaryTerm n := boundaryTerm_nonneg n
      have hslack_nonneg : 0 ≤ δ * barrierSlack E n := by
        have h1 : (1 : ℝ) < (n : ℝ) + E := by
          have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          linarith
        have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
        have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        rw [barrierSlack]
        positivity
      calc c * lowerBarrier A E n
          ≤ c * (lowerBarrier A E n + δ * barrierSlack E n) := by nlinarith
        _ ≤ c * (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * lowerBarrier A E (n - m)) :=
            mul_le_mul_of_nonneg_left hsub_n hcpos.le
        _ = ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (c * lowerBarrier A E (n - m)) := by
            rw [hfactor]
        _ ≤ ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m) := hterm
        _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
            + boundaryTerm n := by linarith
        _ = u n := hrec.symm

/-- Positive liminf (R6 lemma 12): `c ≤ u n` eventually. -/
theorem u_liminf_positive_of_subharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hsub : ∀ᶠ n : ℕ in atTop,
      lowerBarrier A E n + δ * barrierSlack E n
        ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ u n := by
  obtain ⟨c, hcpos, hc⟩ := u_lower_of_subharmonic hA hE hδ hsub
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hH := hc n hn1
  have hH1 : 1 ≤ lowerBarrier A E n := by
    rw [lowerBarrier]
    have h1 : (1 : ℝ) < (n : ℝ) + E := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
    have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
    linarith
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * lowerBarrier A E n := mul_le_mul_of_nonneg_left hH1 hcpos.le
    _ ≤ u n := hH

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

/-- **`u` is bounded below away from 0** (R6): unconditional, via the subharmonic lower barrier fed
by the `o(slack)` mass rate. -/
theorem u_liminf_positive : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ u n := by
  obtain ⟨A, δ, hA, hδ, hsub⟩ :=
    lowerBarrier_kernel_subharmonic_of_rate (le_refl (3:ℝ))
      (kernelMass_rate_vs_slack (le_refl (3:ℝ)))
  exact u_liminf_positive_of_subharmonic hA (le_refl (3:ℝ)) hδ hsub

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

/-- `Σ_t B/(t+1)²` converges (the `1/n` kernel-mass rate, summed over the `√`-spaced chain). -/
lemma summable_const_div_succ_sq (B : ℝ) :
    Summable (fun t : ℕ => B / ((t : ℝ) + 1) ^ 2) := by
  have h2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have hshift : Summable (fun t : ℕ => 1 / (((t : ℝ) + 1)) ^ 2) := by
    have h := (h2.comp_injective (add_left_injective 1))
    refine h.congr (fun t => ?_)
    simp only [Function.comp]
    push_cast
    ring
  simpa [div_eq_mul_inv, mul_comm] using hshift.mul_left B

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

/-- The accumulated residual potential along the chain to the cutoff. -/
noncomputable def potVal (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (e : ℕ → ℝ) : ℕ → ℝ
  | n =>
    if rank n < J then 0
    else e (rank n) + ∑ k ∈ (Finset.range n).attach, P n k.1 * potVal P rank J e k.1
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

lemma hitVal_eq (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (φ : ℕ → ℝ) (n : ℕ) :
    hitVal P rank J φ n
      = if rank n < J then φ n
        else ∑ k ∈ Finset.range n, P n k * hitVal P rank J φ k := by
  rw [hitVal]
  by_cases h : rank n < J
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * hitVal P rank J φ k)]

lemma potVal_eq (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (e : ℕ → ℝ) (n : ℕ) :
    potVal P rank J e n
      = if rank n < J then 0
        else e (rank n) + ∑ k ∈ Finset.range n, P n k * potVal P rank J e k := by
  rw [potVal]
  by_cases h : rank n < J
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * potVal P rank J e k)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 renewal route: the abstract convergence engine (Layer 5 spine)

The renewal / harmonic-Markov-chain route to `u_n → L` (ChatGPT b0f6ab89; replaces the refuted
record-cover whose `1/μ` amplification was proven intrinsic) reduces convergence to a uniform
hit-approximation: for every cutoff `J` the sequence is uniformly close to a convergent "hit value"
`Hit_J`, with error a `J`-tail that vanishes:

  `|u n − Hit_J n| ≤ B·tail J`  eventually,   `Hit_J n → L_J` as `n→∞`,   `tail J → 0`.

Then `limsup u − liminf u ≤ 2 B·tail J` for every `J`, so `u` converges.  This file proves that
engine, design-independent (it takes `Hit`, `Pot`/bound, `tail` abstractly).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Uniform hit-approximation ⟹ convergence.** If `u` is bounded and, for every cutoff `J`,
eventually `|u n − Hit J n| ≤ B·tail J` with `Hit J · → L_J` and `tail J → 0`, then `u` converges. -/
theorem tendsto_of_uniform_hit_approx
    {u : ℕ → ℝ} {Hit : ℕ → ℕ → ℝ} {tail : ℕ → ℝ} {B : ℝ}
    (hu_bddA : BddAbove (Set.range u)) (hu_bddB : BddBelow (Set.range u))
    (hbound : ∀ᶠ J in atTop, ∀ᶠ n in atTop, |u n - Hit J n| ≤ B * tail J)
    (hhit : ∀ᶠ J in atTop, ∃ L, Tendsto (fun n => Hit J n) atTop (𝓝 L))
    (htail : Tendsto tail atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  have hbddU : IsBoundedUnder (· ≤ ·) atTop u := hu_bddA.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop u := hu_bddB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop u := hbddL.isCoboundedUnder_le
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop u := hbddU.isCoboundedUnder_ge
  -- For all large `J`, `limsup u - liminf u ≤ 2 B tail J`.
  have hosc : ∀ᶠ J in atTop, limsup u atTop - liminf u atTop ≤ 2 * (B * tail J) := by
    filter_upwards [hbound, hhit] with J hbJ hhJ
    obtain ⟨L, hL⟩ := hhJ
    -- eventually `u n ≤ Hit J n + B tail J` and `Hit J n - B tail J ≤ u n`
    have hup : ∀ᶠ n in atTop, u n ≤ Hit J n + B * tail J := by
      filter_upwards [hbJ] with n hn
      have := (abs_le.1 hn).2; linarith
    have hlo : ∀ᶠ n in atTop, Hit J n - B * tail J ≤ u n := by
      filter_upwards [hbJ] with n hn
      have := (abs_le.1 hn).1; linarith
    -- limsup u ≤ L + B tail J
    have hHitU : IsBoundedUnder (· ≤ ·) atTop (fun n => Hit J n + B * tail J) :=
      (hL.add_const _).isBoundedUnder_le
    have hHitL : IsBoundedUnder (· ≥ ·) atTop (fun n => Hit J n - B * tail J) :=
      (hL.sub_const _).isBoundedUnder_ge
    have hlimsup : limsup u atTop ≤ L + B * tail J := by
      have h1 : limsup u atTop ≤ limsup (fun n => Hit J n + B * tail J) atTop :=
        limsup_le_limsup hup hcobddU hHitU
      have h2 : limsup (fun n => Hit J n + B * tail J) atTop = L + B * tail J := by
        have := (hL.add_const (B * tail J))
        exact this.limsup_eq
      linarith [h1, h2.le]
    have hliminf : L - B * tail J ≤ liminf u atTop := by
      have h1 : liminf (fun n => Hit J n - B * tail J) atTop ≤ liminf u atTop :=
        liminf_le_liminf hlo hHitL hcobddL
      have h2 : liminf (fun n => Hit J n - B * tail J) atTop = L - B * tail J := by
        have := (hL.sub_const (B * tail J))
        exact this.liminf_eq
      linarith [h1, h2.ge]
    linarith
  -- limsup u - liminf u ≤ 0 by letting tail J → 0.
  have hle : limsup u atTop - liminf u atTop ≤ 0 := by
    have htends : Tendsto (fun J => 2 * (B * tail J)) atTop (𝓝 0) := by
      have : Tendsto (fun J => 2 * (B * tail J)) atTop (𝓝 (2 * (B * 0))) :=
        (htail.const_mul B).const_mul 2
      simpa using this
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htends hosc
  have hge : liminf u atTop ≤ limsup u atTop := liminf_le_limsup hbddU hbddL
  have heq : liminf u atTop = limsup u atTop := le_antisymm hge (by linarith)
  exact ⟨limsup u atTop, tendsto_of_liminf_eq_limsup heq rfl hbddU hbddL⟩

/-- **Layer 2: potential bound (`rec_iter_bound`).** With `Hit`/`Pot` satisfying their fixed-point
equations over the predecessor kernel `P` (probability on `Finset.range n` above the cutoff), and the
recurrence `u n = Σ P·u + d n` with `|d n| ≤ e (rank n)`, the hit-approximation error is controlled
by the potential: `|u n − Hit n| ≤ Pot n`.  Proof by strong induction on `n` (predecessors `k < n`).
Design-independent; the concrete `Hit`/`Pot` are constructed in the kernel layer. -/
theorem rec_iter_bound
    {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {u d e Hit Pot : ℕ → ℝ} {J : ℕ}
    (hP_nonneg : ∀ n k, 0 ≤ P n k)
    (hrec : ∀ n, J ≤ rank n → u n = (∑ k ∈ Finset.range n, P n k * u k) + d n)
    (herr : ∀ n, J ≤ rank n → |d n| ≤ e (rank n))
    (hHit : ∀ n, Hit n = if rank n < J then u n
              else ∑ k ∈ Finset.range n, P n k * Hit k)
    (hPot : ∀ n, Pot n = if rank n < J then 0
              else e (rank n) + ∑ k ∈ Finset.range n, P n k * Pot k) :
    ∀ n, |u n - Hit n| ≤ Pot n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hJ : rank n < J
    · rw [hHit n, hPot n, if_pos hJ, if_pos hJ]; simp
    · have hJ' : J ≤ rank n := not_lt.mp hJ
      rw [hHit n, hPot n, if_neg hJ, if_neg hJ, hrec n hJ', add_comm (e (rank n))]
      have hrw : (∑ k ∈ Finset.range n, P n k * u k) + d n
            - ∑ k ∈ Finset.range n, P n k * Hit k
          = (∑ k ∈ Finset.range n, P n k * (u k - Hit k)) + d n := by
        rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hrw]
      calc |(∑ k ∈ Finset.range n, P n k * (u k - Hit k)) + d n|
          ≤ |∑ k ∈ Finset.range n, P n k * (u k - Hit k)| + |d n| := abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range n, P n k * Pot k) + e (rank n) := by
            gcongr
            · calc |∑ k ∈ Finset.range n, P n k * (u k - Hit k)|
                  ≤ ∑ k ∈ Finset.range n, |P n k * (u k - Hit k)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ k ∈ Finset.range n, P n k * |u k - Hit k| :=
                    Finset.sum_congr rfl (fun k _ => by
                      rw [abs_mul, abs_of_nonneg (hP_nonneg n k)])
                _ ≤ ∑ k ∈ Finset.range n, P n k * Pot k :=
                    Finset.sum_le_sum (fun k hk =>
                      mul_le_mul_of_nonneg_left (ih k (Finset.mem_range.mp hk)) (hP_nonneg n k))
            · exact herr n hJ'

/-- A finite rank-block sum is bounded by the `J`-tail `(∑' e) − ∑_{range J} e`. -/
lemma block_sum_le_tail {e : ℕ → ℝ} (he_nonneg : ∀ j, 0 ≤ e j) (he : Summable e) (J m : ℕ) :
    ∑ j ∈ Finset.Icc J m, e j ≤ (∑' j, e j) - ∑ j ∈ Finset.range J, e j := by
  have hdisj : Disjoint (Finset.Icc J m) (Finset.range J) := by
    rw [Finset.disjoint_left]
    intro a ha hr
    rw [Finset.mem_Icc] at ha; rw [Finset.mem_range] at hr; omega
  have hunion : ∑ j ∈ Finset.Icc J m, e j + ∑ j ∈ Finset.range J, e j
      = ∑ j ∈ Finset.Icc J m ∪ Finset.range J, e j := (Finset.sum_union hdisj).symm
  have hle : ∑ j ∈ Finset.Icc J m ∪ Finset.range J, e j ≤ ∑' j, e j :=
    sum_le_hasSum _ (fun i _ => he_nonneg i) he.hasSum
  linarith [hunion, hle]

/-- **Layer 3 (general, `pot_le_block_sum_of_leave`).** *Fact A for the full kernel.* The full
normalized kernel has small steps, so strict rank-drop fails; but every block is *left downward with
probability ≥ μ* (a window step `m∈[√n,2√n]` drops `rank=⌊ρ√n⌋`, and that mass is `≥μ`). The
contraction-style induction gives `μ·Pot ≤ block-sum`, i.e. `Pot ≤ (1/μ)·tail`.  The `1/μ` is a
single constant on the summable tail — NOT the per-step `μ^{−√N}` compounding that killed the record
route.  `rank` monotone, `P` a probability kernel on `range n`. -/
theorem pot_le_block_sum_of_leave
    {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {e Pot : ℕ → ℝ} {J : ℕ} {μ : ℝ}
    (hJ1 : 1 ≤ J)
    (he_nonneg : ∀ j, 0 ≤ e j)
    (hP_nonneg : ∀ n k, 0 ≤ P n k)
    (hrank_mono : Monotone rank)
    (hP_mass : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k = 1)
    (hP_leave : ∀ n, J ≤ rank n →
        μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rank k < rank n), P n k)
    (hPot : ∀ n, Pot n = if rank n < J then 0
              else e (rank n) + ∑ k ∈ Finset.range n, P n k * Pot k) :
    ∀ n, μ * Pot n ≤ ∑ j ∈ Finset.Icc J (rank n), e j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hPot n]
    by_cases hJ : rank n < J
    · rw [if_pos hJ, Finset.Icc_eq_empty (by omega)]; simp
    · rw [if_neg hJ]
      have hJ' : J ≤ rank n := not_lt.mp hJ
      set T := ∑ j ∈ Finset.Icc J (rank n), e j with hT
      set Tm := ∑ j ∈ Finset.Icc J (rank n - 1), e j with hTm
      have hTm_nonneg : 0 ≤ Tm := Finset.sum_nonneg (fun j _ => he_nonneg j)
      have hTsplit : T = Tm + e (rank n) := by
        rw [hT, hTm]
        have hrn : rank n = (rank n - 1) + 1 := by omega
        conv_lhs => rw [hrn]
        rw [Finset.sum_Icc_succ_top (by omega : J ≤ (rank n - 1) + 1), ← hrn]
      -- `μ · Σ P·Pot ≤ Σ P·T_k`
      have hμPot : μ * (∑ k ∈ Finset.range n, P n k * Pot k)
          ≤ ∑ k ∈ Finset.range n, P n k * (∑ j ∈ Finset.Icc J (rank k), e j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [show μ * (P n k * Pot k) = P n k * (μ * Pot k) by ring]
        exact mul_le_mul_of_nonneg_left (ih k (Finset.mem_range.mp hk)) (hP_nonneg n k)
      -- split `range n` into rank-drop and rank-stay parts
      have hfP := Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun k => rank k < rank n) (fun k => P n k)
      have hff := Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun k => rank k < rank n) (fun k => P n k * (∑ j ∈ Finset.Icc J (rank k), e j))
      rw [hP_mass n hJ'] at hfP
      set Ddrop := ∑ k ∈ (Finset.range n).filter (fun k => rank k < rank n), P n k with hDdrop
      set Dsame := ∑ k ∈ (Finset.range n).filter (fun k => ¬ rank k < rank n), P n k with hDsame
      have hDsame_nonneg : 0 ≤ Dsame := Finset.sum_nonneg (fun k _ => hP_nonneg n k)
      have hDleave : μ ≤ Ddrop := hP_leave n hJ'
      -- `Σ P·T_k ≤ Ddrop·Tm + Dsame·T`
      have hbound : ∑ k ∈ Finset.range n, P n k * (∑ j ∈ Finset.Icc J (rank k), e j)
          ≤ Ddrop * Tm + Dsame * T := by
        rw [← hff, hDdrop, hDsame, Finset.sum_mul, Finset.sum_mul]
        refine add_le_add (Finset.sum_le_sum (fun k hk => ?_))
          (Finset.sum_le_sum (fun k hk => ?_))
        · rw [Finset.mem_filter, Finset.mem_range] at hk
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (by omega)) (fun j _ _ => he_nonneg j))
            (hP_nonneg n k)
        · rw [Finset.mem_filter, Finset.mem_range] at hk
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (hrank_mono hk.1.le)) (fun j _ _ => he_nonneg j))
            (hP_nonneg n k)
      -- assemble: μ·Pot n = μ·e + μ·ΣPPot ≤ μ·e + Ddrop·Tm + Dsame·T ≤ T
      rw [mul_add]
      have he := he_nonneg (rank n)
      have hkey : μ * e (rank n) + (Ddrop * Tm + Dsame * T) ≤ T := by
        have hDd : Ddrop = 1 - Dsame := by linarith [hfP]
        have hDsame_le : Dsame ≤ 1 - μ := by linarith [hfP, hDleave]
        rw [hTsplit, hDd]
        nlinarith [mul_nonneg (sub_nonneg.mpr hDsame_le) he, he, hTm_nonneg, hDsame_nonneg]
      linarith [hμPot, hbound, hkey]

/-- The `J`-tail `(∑' e) − ∑_{range J} e` of a summable series tends to `0`. -/
lemma tail_tendsto_zero {e : ℕ → ℝ} (he : Summable e) :
    Tendsto (fun J => (∑' j, e j) - ∑ j ∈ Finset.range J, e j) atTop (𝓝 0) := by
  have h := he.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun J => (∑' j, e j) - ∑ j ∈ Finset.range J, e j) atTop
      (𝓝 ((∑' j, e j) - ∑' j, e j)) := tendsto_const_nhds.sub h
  simpa using hlim

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

/-- Residual of the normalized recurrence. -/
noncomputable def dres (n : ℕ) : ℝ := u n - ∑ k ∈ Finset.range n, Pker n k * u k

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

/-- The recurrence in normalized form holds by definition of the residual. -/
lemma u_eq_Pker_sum_add_dres (n : ℕ) :
    u n = (∑ k ∈ Finset.range n, Pker n k * u k) + dres n := by
  unfold dres; ring

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

/-- **Residual formula** (`d_eq`): `d n = u n − (u n − boundaryTerm n)/kernelMass n`. -/
lemma dres_eq {n : ℕ} (hn : 2 ≤ n) :
    dres n = u n - (u n - boundaryTerm n) / kernelMass n := by
  unfold dres
  rw [Pker_sum_mul n hn u]
  rw [show (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) = u n - boundaryTerm n by
    have hrec := u_recurrence n hn; linarith]

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- A `√`-gap exceeding `1/3` forces a strict rank drop (since `rnk = ⌊3√·⌋`). -/
lemma rnk_lt_of_sqrt_gap {n k : ℕ} (h : (1:ℝ)/3 < Real.sqrt n - Real.sqrt k) :
    rnk k < rnk n := by
  unfold rnk
  rw [← Nat.add_one_le_iff]
  apply Nat.le_floor
  push_cast
  have hfk : (⌊3 * Real.sqrt k⌋₊ : ℝ) ≤ 3 * Real.sqrt k := Nat.floor_le (by positivity)
  linarith

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

/-- **Window steps drop rank.** If `√n < m` (the window lower edge `a₀=1`) then the predecessor
`n − m` has strictly smaller rank: `√n − √(n−m) > 1/2 > 1/3`. -/
lemma window_rank_drop {n m : ℕ} (hn : 1 ≤ n) (hmn : m < n)
    (hmlb : Real.sqrt (n : ℝ) < (m : ℝ)) :
    rnk (n - m) < rnk n := by
  apply rnk_lt_of_sqrt_gap
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hble : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (le_of_lt hmn)]
  have hprod : (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
      * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) = (m : ℝ) := by
    have e1 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    have e2 : Real.sqrt ((n - m : ℕ) : ℝ) ^ 2 = (n : ℝ) - m := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  have hsumpos : 0 < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by linarith [Real.sqrt_nonneg ((n - m : ℕ) : ℝ)]
  have hgap : Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)
      = (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hsumpos)]; exact hprod
  rw [hgap, lt_div_iff₀ hsumpos]
  nlinarith [hmlb, hble, ha]

section
end

set_option maxHeartbeats 1000000 in
/-- **Residual is block-summable** (`herr`): `|dres n| ≤ errFn (rnk n)` eventually, with `errFn ≥ 0`
summable.  This is the "small summable residual" input both endgame routes need.  Scale via
`rnk_sqrt_bounds`: `(j/3)² ≤ n < ((j+1)/3)²`, `1/n ≤ 9/j² ≤ 36/(j+1)²`, `n² < ((j+1)/3)⁴ ≤ (16/81)j⁴`,
`e^{−C√n} ≤ e^{−Cj/3}`. -/
theorem dres_block_bound :
    ∃ errFn : ℕ → ℝ, (∀ j, 0 ≤ errFn j) ∧ Summable errFn ∧
      ∀ᶠ n in Filter.atTop, |dres n| ≤ errFn (rnk n) := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hCpos := C_pos
  refine ⟨fun j => 72 * M * K / ((j : ℝ) + 1) ^ 2
      + (32 / 81) * (j : ℝ) ^ 4 * Real.exp (-(C / 3) * (j : ℝ)), ?_, ?_, ?_⟩
  · intro j; have hM := hMpos.le; have hK := hKpos.le; positivity
  · apply Summable.add
    · exact summable_const_div_succ_sq (72 * M * K)
    · have h := summable_pow_mul_exp_neg (show (0 : ℝ) < C / 3 by linarith) 4
      exact (h.mul_left (32 / 81)).congr (fun j => by ring)
  · have hhalf : ∀ᶠ n : ℕ in Filter.atTop, K / (n : ℝ) ≤ 1 / 2 := by
      have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
      exact htend.eventually_le_const (by norm_num)
    filter_upwards [hMev, hKev, hhalf, Filter.eventually_ge_atTop 2]
      with n hMn hKn hhalfn hn2
    have hn1 : (1 : ℕ) ≤ n := by omega
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    -- kernelMass ≥ 1/2 > 0
    obtain ⟨hSlo, _⟩ := abs_le.1 hKn
    have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hhalfn]
    have hSpos : (0 : ℝ) < kernelMass n := by linarith
    -- nonneg facts
    have hu0 : 0 ≤ u n := (u_pos hn1).le
    have hb0 : 0 ≤ boundaryTerm n := boundaryTerm_nonneg n
    have hSabs : |kernelMass n - 1| ≤ K / (n : ℝ) := hKn
    -- sqrt/scale bounds
    obtain ⟨hjle, hjlt⟩ := rnk_sqrt_bounds n
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnR
    have hj1 : (1 : ℝ) ≤ (rnk n : ℝ) := by
      have h3 : (3 : ℝ) ≤ (rnk n : ℝ) := by
        have : (3 : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by linarith
        calc (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
          _ ≤ (rnk n : ℝ) := by
              rw [Nat.cast_le]; unfold rnk; exact Nat.le_floor (by push_cast; linarith)
      linarith
    have hjpos : (0 : ℝ) < (rnk n : ℝ) := by linarith
    have hsqrt_lb : (rnk n : ℝ) / 3 ≤ Real.sqrt (n : ℝ) := by linarith
    have hsqrt_ub : Real.sqrt (n : ℝ) < ((rnk n : ℝ) + 1) / 3 := by linarith
    have hsqsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    -- n ≥ (j/3)²  ⟹  1/n ≤ 9/j²
    have hn_lb : ((rnk n : ℝ) / 3) ^ 2 ≤ (n : ℝ) := by
      rw [← hsqsq]; apply pow_le_pow_left₀ (by positivity) hsqrt_lb
    have hinv : (1 : ℝ) / (n : ℝ) ≤ 9 / (rnk n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hnpos (by positivity)]
      nlinarith [hn_lb, hjpos]
    -- n < ((j+1)/3)²  ⟹  n² < ((j+1)/3)⁴
    have hn_ub : (n : ℝ) < (((rnk n : ℝ) + 1) / 3) ^ 2 := by
      rw [← hsqsq]; apply pow_lt_pow_left₀ hsqrt_ub hsqrtpos.le (by norm_num)
    have hnsq_ub : (n : ℝ) ^ 2 < (((rnk n : ℝ) + 1) / 3) ^ 4 := by
      have h4 : (((rnk n : ℝ) + 1) / 3) ^ 4 = ((((rnk n : ℝ) + 1) / 3) ^ 2) ^ 2 := by ring
      rw [h4]; apply pow_lt_pow_left₀ hn_ub (by positivity) (by norm_num)
    -- e^{−C√n} ≤ e^{−Cj/3}
    have hexp : Real.exp (-C * Real.sqrt (n : ℝ)) ≤ Real.exp (-(C / 3) * (rnk n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (C / 3) * (rnk n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by nlinarith [hsqrt_lb, hCpos.le]
      linarith
    -- σ(n) ≤ n²  ⟹  boundaryTerm n ≤ n² e^{−C√n}
    have hb_ub : boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := by
      unfold boundaryTerm
      apply mul_le_mul_of_nonneg_right (sigmaR_le_square hn1) (Real.exp_nonneg _)
    -- the dres bound
    rw [dres_eq (by omega)]
    have hform : |u n - (u n - boundaryTerm n) / kernelMass n|
        = |u n * (kernelMass n - 1) + boundaryTerm n| / kernelMass n := by
      have hinside : u n - (u n - boundaryTerm n) / kernelMass n
          = (u n * (kernelMass n - 1) + boundaryTerm n) / kernelMass n := by
        field_simp; ring
      rw [hinside, abs_div, abs_of_pos hSpos]
    rw [hform]
    -- numerator ≤ M·(K/n) + boundaryTerm n
    have hnum : |u n * (kernelMass n - 1) + boundaryTerm n| ≤ M * (K / (n : ℝ)) + boundaryTerm n := by
      calc |u n * (kernelMass n - 1) + boundaryTerm n|
          ≤ |u n * (kernelMass n - 1)| + |boundaryTerm n| := abs_add_le _ _
        _ = u n * |kernelMass n - 1| + boundaryTerm n := by
            rw [abs_mul, abs_of_nonneg hu0, abs_of_nonneg hb0]
        _ ≤ M * (K / (n : ℝ)) + boundaryTerm n := by
            have hstep : u n * |kernelMass n - 1| ≤ M * (K / (n : ℝ)) :=
              le_trans (mul_le_mul_of_nonneg_left hSabs hu0)
                (mul_le_mul_of_nonneg_right hMn (by positivity))
            linarith [hstep]
    -- divide by S ≥ 1/2 and bound by errFn
    have hdiv : |u n * (kernelMass n - 1) + boundaryTerm n| / kernelMass n
        ≤ 2 * (M * (K / (n : ℝ)) + boundaryTerm n) := by
      rw [div_le_iff₀ hSpos]
      have hmkb : 0 ≤ M * (K / (n : ℝ)) + boundaryTerm n :=
        add_nonneg (mul_nonneg hMpos.le (div_nonneg hKpos.le hnpos.le)) hb0
      nlinarith [hnum, hSge, hmkb]
    refine le_trans hdiv ?_
    -- 2(MK/n + b) ≤ errFn (rnk n)
    have hMK : 0 ≤ M * K := by positivity
    have hinv2 : (1 : ℝ) / (n : ℝ) ≤ 36 / ((rnk n : ℝ) + 1) ^ 2 := by
      have h9 : (9 : ℝ) / (rnk n : ℝ) ^ 2 ≤ 36 / ((rnk n : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hj1]
      linarith [hinv, h9]
    have ht1 : 2 * (M * (K / (n : ℝ))) ≤ 72 * M * K / ((rnk n : ℝ) + 1) ^ 2 := by
      have hrw : 2 * (M * (K / (n : ℝ))) = 2 * M * K * (1 / (n : ℝ)) := by ring
      rw [hrw]
      calc 2 * M * K * (1 / (n : ℝ))
          ≤ 2 * M * K * (36 / ((rnk n : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hinv2 (by positivity)
        _ = 72 * M * K / ((rnk n : ℝ) + 1) ^ 2 := by ring
    have ht2 : 2 * boundaryTerm n ≤ (32 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
      have hb2 : boundaryTerm n ≤ (((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
        calc boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := hb_ub
          _ ≤ (((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
              apply mul_le_mul (le_of_lt hnsq_ub) hexp (Real.exp_nonneg _) (by positivity)
      have hpoly : (((rnk n : ℝ) + 1) / 3) ^ 4 ≤ (16 / 81) * (rnk n : ℝ) ^ 4 := by
        have hle : (rnk n : ℝ) + 1 ≤ 2 * (rnk n : ℝ) := by linarith [hj1]
        have hexp4 : ((rnk n : ℝ) + 1) ^ 4 ≤ 16 * (rnk n : ℝ) ^ 4 := by
          nlinarith [pow_le_pow_left₀ (show (0:ℝ) ≤ (rnk n : ℝ) + 1 by positivity) hle 4]
        rw [div_pow, show (3:ℝ) ^ 4 = 81 by norm_num]
        linarith [hexp4]
      calc 2 * boundaryTerm n
          ≤ 2 * ((((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ))) := by linarith
        _ ≤ 2 * ((16 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ))) := by
            gcongr
        _ = (32 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by ring
    linarith [ht1, ht2]

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

/-- **Leave probability** (`hP_leave`): a uniform positive mass of the normalized kernel goes to
strictly lower rank.  Window steps `m ∈ (√n, 2√n]` carry mass `≥ ν` (`kernelWindow_one_two_pos`) and
drop rank (`window_rank_drop`); dividing by `kernelMass n ≤ 2` gives `≥ ν/2`. -/
theorem hP_leave_partition :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
  obtain ⟨ν, hνpos, hνmass⟩ := kernelWindow_one_two_pos
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hone : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  refine ⟨ν / 2, by positivity, ?_⟩
  filter_upwards [hνmass, hKev, hone, Filter.eventually_ge_atTop 2] with n hνn hKn hKn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKn
  have hS2 : kernelMass n ≤ 2 := by linarith [hSup, hKn1]
  have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hSlo, hKn1]
  have hSpos : (0 : ℝ) < kernelMass n := by linarith
  -- main inequality: kernelWindow 1 2 n / kernelMass n ≤ leave-sum
  have hkey : kernelWindow 1 2 n / kernelMass n
      ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
    -- reindex the window mass to predecessor coordinate and embed into the rank-drop filter
    have hreflect : kernelWindow 1 2 n / kernelMass n
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            (if 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
                ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
              then Pker n k else 0) := by
      rw [kernelWindow, ← sum_Icc_reflect_sub n
        (fun m => if 1 * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
          then erdosWeight n m else 0), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hw : 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
          ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
      · rw [if_pos hw, if_pos hw]
        unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
      · rw [if_neg hw, if_neg hw, zero_div]
    rw [hreflect, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hd := window_rank_drop (n := n) (m := n - k) (by omega) (by omega) (by
        rw [one_mul] at hw1; exact hw1)
      rwa [Nat.sub_sub_self (by omega : k ≤ n)] at hd
    · intro k _ _; exact Pker_nonneg n k
  refine le_trans ?_ hkey
  rw [le_div_iff₀ hSpos]
  nlinarith [hνn, hS2, hνpos]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 assembly: `erdos_partition_limit_exists` modulo the hard core (Fact B)

Instantiates the renewal spine to the partition kernel: with all Layer-1 kernel facts proven
(`Pker_mass`, `dres_block_bound`, `hP_leave_partition`) plus the well-founded `hitVal`/`potVal`,
`rec_iter_bound` + `pot_le_block_sum_of_leave` + `block_sum_le_tail` give the uniform
hit-approximation `|u n − hitVal_J n| ≤ (1/μ)·tail_J`, and the convergence engine
`tendsto_of_uniform_hit_approx` then yields convergence — *modulo* the single hard analytic
hypothesis (Fact B): for cofinitely many cutoffs `J`, the hit value `hitVal Pker rnk J u` converges.
Opus-authored.
-/

noncomputable section

open Filter Topology

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
theorem solution
    (hhit : ∀ᶠ J : ℕ in atTop,
        ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨c, hcpos, hcev⟩ := u_liminf_positive
  obtain ⟨errFn, herr_nn, herr_sum, herr_ev⟩ := dres_block_bound
  obtain ⟨μ, hμpos, hμ_ev⟩ := hP_leave_partition
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- `u` is globally bounded
  have hBddA : BddAbove (Set.range u) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
    refine ⟨max M (∑ k ∈ Finset.range N, |u k|), ?_⟩
    rintro y ⟨n, rfl⟩
    by_cases h : n < N
    · refine le_trans (le_trans (le_abs_self (u n)) ?_) (le_max_right _ _)
      exact Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg (u k))
        (Finset.mem_range.mpr h)
    · exact le_trans (hN n (by omega)) (le_max_left _ _)
  have hBddB : BddBelow (Set.range u) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [u]
    · exact (u_pos hpos).le
  -- combined eventual kernel facts
  have hhalf : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  have hcomb : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ (1 : ℝ) / 2 ≤ kernelMass n
      ∧ |dres n| ≤ errFn (rnk n)
      ∧ μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
    filter_upwards [herr_ev, hμ_ev, hKev, hhalf, eventually_ge_atTop 2]
      with n h1 h2 h3 h4 h5
    refine ⟨h5, ?_, h1, h2⟩
    obtain ⟨hlo, _⟩ := abs_le.1 h3
    linarith [h4]
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hcomb
  -- the uniform hit-approximation `|u n − hitVal_J n| ≤ (1/μ)·tail_J`
  have hbound : ∀ᶠ J : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      |u n - hitVal Pker rnk J u n|
        ≤ 1 / μ * ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) := by
    filter_upwards [eventually_ge_atTop (3 * N0 + 3), eventually_ge_atTop 1] with J hJ hJ1
    apply Eventually.of_forall
    intro n
    have hfact : ∀ m, J ≤ rnk m → 2 ≤ m ∧ (1 : ℝ) / 2 ≤ kernelMass m
        ∧ |dres m| ≤ errFn (rnk m)
        ∧ μ ≤ ∑ k ∈ (Finset.range m).filter (fun k => rnk k < rnk m), Pker m k := by
      intro m hm
      exact hN0 m (rnk_ge_of (by omega))
    have hrib := rec_iter_bound (P := Pker) (rank := rnk) (u := u) (d := dres) (e := errFn)
      (Hit := hitVal Pker rnk J u) (Pot := potVal Pker rnk J errFn) (J := J)
      (fun n k => Pker_nonneg n k)
      (fun m _ => u_eq_Pker_sum_add_dres m)
      (fun m hm => (hfact m hm).2.2.1)
      (hitVal_eq Pker rnk J u)
      (potVal_eq Pker rnk J errFn)
    have hple := pot_le_block_sum_of_leave (P := Pker) (rank := rnk) (e := errFn)
      (Pot := potVal Pker rnk J errFn) (J := J) (μ := μ) (by omega)
      herr_nn (fun n k => Pker_nonneg n k) rnk_mono
      (fun m hm => Pker_mass (hfact m hm).1
        (ne_of_gt (lt_of_lt_of_le (by norm_num) (hfact m hm).2.1)))
      (fun m hm => (hfact m hm).2.2.2)
      (potVal_eq Pker rnk J errFn)
    have hb1 := hrib n
    have hb2 := hple n
    have hb3 := block_sum_le_tail herr_nn herr_sum J (rnk n)
    have hmul : μ * potVal Pker rnk J errFn n
        ≤ (∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j := le_trans hb2 hb3
    have hPotle : potVal Pker rnk J errFn n
        ≤ ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) / μ := by
      rw [le_div_iff₀ hμpos]; nlinarith [hmul]
    calc |u n - hitVal Pker rnk J u n| ≤ potVal Pker rnk J errFn n := hb1
      _ ≤ ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) / μ := hPotle
      _ = 1 / μ * ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) := by ring
  obtain ⟨a, ha⟩ := tendsto_of_uniform_hit_approx (u := u)
    (Hit := fun J n => hitVal Pker rnk J u n)
    (tail := fun J => (∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j)
    (B := 1 / μ) hBddA hBddB hbound hhit (tail_tendsto_zero herr_sum)
  refine ⟨a, ?_, ha⟩
  have hca : c ≤ a := ge_of_tendsto ha hcev
  linarith [hcpos]
