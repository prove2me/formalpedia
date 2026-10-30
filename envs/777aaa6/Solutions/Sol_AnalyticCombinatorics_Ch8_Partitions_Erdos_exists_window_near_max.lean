-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_window_near_max
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:49:17.963197+00:00
-- url     : https://prove2.me/submissions/a234aef7-9bd5-47d6-ad1e-1f9c87582422

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
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

lemma erdosWeight_nonneg_of_lt {n m : ℕ} (hmn : m < n) :
    0 ≤ erdosWeight n m := by
  dsimp [erdosWeight]
  have hden : 0 < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hmn
  exact mul_nonneg (div_nonneg (sigmaR_nonneg m) hden.le) (Real.exp_pos _).le

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
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

open Filter
open scoped BigOperators Topology Interval

noncomputable section

local notation "σR" => Sigma.sigmaR

lemma sqrt_sub_le_nine_tenths_sqrt {n r : ℕ} (hr : 2 * r ≤ n) :
    Real.sqrt (r : ℝ) ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by
  have hr_nonneg : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by positivity
  have hsq :
      Real.sqrt (r : ℝ) ^ 2 ≤
        ((9 / 10 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (r : ℝ))]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    norm_num
    nlinarith [show (2 : ℝ) * (r : ℝ) ≤ (n : ℝ) by exact_mod_cast hr]
  exact (sq_le_sq₀ hr_nonneg hright_nonneg).mp hsq

lemma sqrt_drop_ge_right_half {n m : ℕ}
    (hmn : m ≤ n) (hright : n < 2 * m) :
    (1 / 10 : ℝ) * Real.sqrt (n : ℝ) ≤
      Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hsub_half : 2 * (n - m) ≤ n := by omega
  have hsqrt_le :=
    sqrt_sub_le_nine_tenths_sqrt (n := n) (r := n - m) hsub_half
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma erdosWeight_le_right_half {n m : ℕ}
    (hm : m ∈ Finset.Icc 1 (n - 1)) (hright : n < 2 * m) :
    erdosWeight n m ≤
      (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  have hmI := Finset.mem_Icc.mp hm
  have hm_pos : 1 ≤ m := hmI.1
  have hmn : m < n := by omega
  have hmn_le : m ≤ n := le_of_lt hmn
  have hden_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hden_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hden_pos_nat
  have hden_ge_one : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hsig := Erdos.sigmaR_le_square (n := m) hm_pos
  have hm_le_n_real : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn_le
  have hm_sq_le_n_sq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ)) (by positivity : 0 ≤ (n : ℝ))).mpr hm_le_n_real
  have hsig_le_n_sq : σR m ≤ (n : ℝ) ^ 2 := hsig.trans hm_sq_le_n_sq
  have hfrac_le :
      σR m / ((n - m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hfrac_le_sig : σR m / ((n - m : ℕ) : ℝ) ≤ σR m := by
      rw [div_le_iff₀ hden_pos]
      have hmul := mul_le_mul_of_nonneg_left hden_ge_one (Erdos.sigmaR_nonneg m)
      simpa [one_mul] using hmul
    exact hfrac_le_sig.trans hsig_le_n_sq
  have hdrop := sqrt_drop_ge_right_half (n := n) (m := m) hmn_le hright
  have hexp :
      Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) ≤
        Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hCmul := mul_le_mul_of_nonneg_left hdrop C_pos.le
    nlinarith
  have hfrac_nonneg :
      0 ≤ σR m / ((n - m : ℕ) : ℝ) :=
    div_nonneg (Erdos.sigmaR_nonneg m) hden_pos.le
  calc
    erdosWeight n m
        = σR m / ((n - m : ℕ) : ℝ) *
            Real.exp (-C *
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) := rfl
    _ ≤ (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          exact mul_le_mul hfrac_le hexp (Real.exp_pos _).le (by positivity)

lemma right_half_kernel_sum_le (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0) ≤
      (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  classical
  let Bn : ℝ := (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))
  have hterm :
      ∀ m ∈ Finset.Icc 1 (n - 1),
        (if n < 2 * m then erdosWeight n m else 0) ≤ Bn := by
    intro m hm
    by_cases hright : n < 2 * m
    · simpa [Bn, hright] using erdosWeight_le_right_half (n := n) (m := m) hm hright
    · have hBn_nonneg : 0 ≤ Bn := by
        dsimp [Bn]
        positivity
      simp [hright, hBn_nonneg]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if n < 2 * m then erdosWeight n m else 0) ≤
        ∑ m ∈ Finset.Icc 1 (n - 1), Bn := by
    exact Finset.sum_le_sum hterm
  have hcard : ((Finset.Icc 1 (n - 1)).card : ℝ) ≤ (n : ℝ) := by
    have hcard_nat : (Finset.Icc 1 (n - 1)).card ≤ n := by
      have hsubset : Finset.Icc 1 (n - 1) ⊆ Finset.range n := by
        intro m hm
        have hmge : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
        exact Finset.mem_range.mpr (by omega)
      have h := Finset.card_le_card hsubset
      rw [Finset.card_range] at h
      exact h
    exact_mod_cast hcard_nat
  calc
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1), Bn := hsum
    _ = ((Finset.Icc 1 (n - 1)).card : ℝ) * Bn := by
          simp [Bn, nsmul_eq_mul]
    _ ≤ (n : ℝ) * Bn := by
          exact mul_le_mul_of_nonneg_right hcard (by dsimp [Bn]; positivity)
    _ = (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          dsimp [Bn]
          ring

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: §8 the record pullback with summable defect (R7 core)

ChatGPT-Pro consult (task 19e127f1) established that the intended record-cover lemmas are NOT
derivable from boundedness + forward-fill + `b(n)→0` alone (explicit slowly-oscillating
countermodel).  The honest route needs the **one-step pullback with a quantitative defect**

  `Δ_N = (|b(N)| + M·|S_N − 1| + M·prefixTail(N)) / μ`,

summable on the `t = √n` scale for the genuine partition kernel.  This file banks the exact
one-step pullback (running-max version).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Filter Finset
open scoped BigOperators Topology
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution {a b μ M : ℝ} {N N₀ : ℕ} (hN2 : 2 ≤ N) (hμ : 0 < μ)
    (hMnonneg : 0 ≤ M)
    (hMbound : ∀ k : ℕ, k ≤ N → u k ≤ M)
    (hmax : ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N)
    (hwin : μ ≤ kernelWindow a b N)
    (hprefix : ∀ m : ℕ, m ∈ Finset.Icc 1 (N - 1) → ¬ (N₀ ≤ N - m) → N < 2 * m) :
    ∃ m : ℕ, m ∈ Finset.Icc 1 (N - 1) ∧
      (a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)) ∧
      u N - (|boundaryTerm N| + M * |kernelMass N - 1|
        + M * ((N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)))) / μ ≤ u (N - m) := by
  classical
  set s : Finset ℕ := Finset.Icc 1 (N - 1) with hs
  set win : ℕ → Prop := fun m => a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)
    with hwindef
  set R : ℝ := (N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; positivity
  set defect : ℝ := |boundaryTerm N| + M * |kernelMass N - 1| + M * R with hdefdef
  have hdefnn : 0 ≤ defect := by
    rw [hdefdef]
    have h1 := abs_nonneg (boundaryTerm N)
    have h2 : 0 ≤ M * |kernelMass N - 1| := mul_nonneg hMnonneg (abs_nonneg _)
    have h3 : 0 ≤ M * R := mul_nonneg hMnonneg hRnn
    linarith
  have hWnn : ∀ m ∈ s, 0 ≤ erdosWeight N m := fun m hm => erdosWeight_nonneg_of_mem hm
  have huN_nn : 0 ≤ u N := (u_pos (show 1 ≤ N by omega)).le
  have huN_le_M : u N ≤ M := hMbound N (le_refl N)
  have hkw : 0 < kernelWindow a b N := lt_of_lt_of_le hμ hwin
  -- window finset nonempty
  set sWin : Finset ℕ := s.filter win with hsWin
  have hsWin_ne : sWin.Nonempty := by
    rw [hsWin, Finset.filter_nonempty_iff]
    by_contra hcon
    push_neg at hcon
    have hz : kernelWindow a b N = 0 := by
      rw [kernelWindow, ← hs]
      exact Finset.sum_eq_zero (fun m hm => if_neg (hcon m hm))
    linarith [hwin]
  obtain ⟨mstar, hmstar_mem, hmstar_max⟩ := Finset.exists_max_image sWin (fun m => u (N - m)) hsWin_ne
  obtain ⟨hmstar_s, hmstar_win⟩ := Finset.mem_filter.mp hmstar_mem
  set v : ℝ := u (N - mstar) with hvdef
  refine ⟨mstar, hmstar_s, hmstar_win, ?_⟩
  have hrec : u N = (∑ m ∈ s, erdosWeight N m * u (N - m)) + boundaryTerm N :=
    u_recurrence N hN2
  -- split the kernel sum into window / complement
  have hsplitsum : (∑ m ∈ s, erdosWeight N m * u (N - m))
      = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
        + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  -- window part ≤ v · kernelWindow
  have hwin_part : (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
      ≤ v * kernelWindow a b N := by
    rw [kernelWindow, ← hs, Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]
      have hle : u (N - m) ≤ v := hmstar_max m (Finset.mem_filter.mpr ⟨hm, hw⟩)
      calc erdosWeight N m * u (N - m) ≤ erdosWeight N m * v :=
            mul_le_mul_of_nonneg_left hle (hWnn m hm)
        _ = v * erdosWeight N m := by ring
    · rw [if_neg hw, if_neg hw, mul_zero]
  -- complement part ≤ uN·(mass − window) + M·R
  have hmasswin : kernelMass N - kernelWindow a b N
      = ∑ m ∈ s, if win m then 0 else erdosWeight N m := by
    rw [kernelMass, kernelWindow, ← hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  have hcomp_part : (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m))
      ≤ u N * (kernelMass N - kernelWindow a b N) + M * R := by
    have hbound : ∀ m ∈ s, (if win m then 0 else erdosWeight N m * u (N - m))
        ≤ (if win m then 0 else erdosWeight N m * u N)
          + M * (if N < 2 * m then erdosWeight N m else 0) := by
      intro m hm
      have hMite : 0 ≤ M * (if N < 2 * m then erdosWeight N m else 0) := by
        have hi : (0:ℝ) ≤ (if N < 2 * m then erdosWeight N m else 0) := by
          split_ifs with h; exacts [hWnn m hm, le_rfl]
        exact mul_nonneg hMnonneg hi
      by_cases hw : win m
      · rw [if_pos hw, if_pos hw]; linarith
      · rw [if_neg hw, if_neg hw]
        by_cases hpre : N₀ ≤ N - m
        · have hle : u (N - m) ≤ u N := hmax (N - m) hpre (Nat.sub_le N m)
          nlinarith [mul_le_mul_of_nonneg_left hle (hWnn m hm), hMite]
        · have hN2m : N < 2 * m := hprefix m hm hpre
          rw [if_pos hN2m]
          have hle : u (N - m) ≤ M := hMbound (N - m) (Nat.sub_le N m)
          nlinarith [mul_le_mul_of_nonneg_left hle (hWnn m hm),
            mul_nonneg (hWnn m hm) huN_nn]
    calc (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m))
        ≤ ∑ m ∈ s, ((if win m then 0 else erdosWeight N m * u N)
            + M * (if N < 2 * m then erdosWeight N m else 0)) := Finset.sum_le_sum hbound
      _ = (∑ m ∈ s, if win m then 0 else erdosWeight N m * u N)
            + M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = u N * (kernelMass N - kernelWindow a b N)
            + M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) := by
          rw [hmasswin]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          by_cases hw : win m
          · rw [if_pos hw, if_pos hw, mul_zero]
          · rw [if_neg hw, if_neg hw, mul_comm]
      _ ≤ u N * (kernelMass N - kernelWindow a b N) + M * R := by
          have hrh : (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ R := by
            rw [hRdef, hs]; exact right_half_kernel_sum_le N
          have : M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ M * R :=
            mul_le_mul_of_nonneg_left hrh hMnonneg
          linarith
  -- combine
  have hrec2 : u N = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
      + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) + boundaryTerm N := by
    rw [hrec, hsplitsum]
  have hbnd : u N ≤ v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N) + M * R
      + boundaryTerm N := by
    linarith [hrec2, hwin_part, hcomp_part]
  -- kernelWindow · (uN − v) ≤ defect
  have hkey : kernelWindow a b N * (u N - v) ≤ defect := by
    have hb : boundaryTerm N ≤ |boundaryTerm N| := le_abs_self _
    have huk : u N * (kernelMass N - 1) ≤ M * |kernelMass N - 1| := by
      calc u N * (kernelMass N - 1) ≤ u N * |kernelMass N - 1| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) huN_nn
        _ ≤ M * |kernelMass N - 1| :=
            mul_le_mul_of_nonneg_right huN_le_M (abs_nonneg _)
    have hexp : kernelWindow a b N * (u N - v)
        = u N - (v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N))
          + u N * (kernelMass N - 1) := by ring
    rw [hexp, hdefdef]
    linarith [hbnd, hb, huk]
  -- conclude v ≥ uN − defect/μ
  have hdiff : u N - v ≤ defect / μ := by
    rcases le_or_gt (u N - v) 0 with hle | hlt
    · have : (0:ℝ) ≤ defect / μ := by positivity
      linarith
    · rw [le_div_iff₀ hμ]
      have : u N - v ≤ defect / kernelWindow a b N := by
        rw [le_div_iff₀ hkw]; linarith [hkey]
      calc (u N - v) * μ ≤ (defect / kernelWindow a b N) * μ :=
            mul_le_mul_of_nonneg_right this hμ.le
        _ ≤ (defect / μ) * μ := by
            apply mul_le_mul_of_nonneg_right _ hμ.le
            gcongr
        _ = defect := by field_simp
  show u N - defect / μ ≤ v
  linarith [hdiff]
