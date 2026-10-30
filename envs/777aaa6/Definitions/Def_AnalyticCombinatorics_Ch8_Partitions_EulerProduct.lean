-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
-- name    : AnalyticCombinatorics_Ch8_Partitions_EulerProduct
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:48:07.055753+00:00
-- url     : https://prove2.me/theorems/109586ce-db00-4b14-b415-9995d8c76dac
-- title:
--   Euler Product mathematical objects
-- statement:
--   For natural K and n, partsLE(K,n) counts partitions of n with every part at most K. A multiplicity vector q:Fin K -> Nat assigns q(i) copies of the positive part i+1; multiplicityWeight is their weighted sum, and countsMultiset forms their multiset. partitionOfCountsAt constructs a partition from a vector of weight n; boundedPartitionEquivCounts is the explicit bijection between such vectors and bounded partitions. weightFiberFintype supplies their finite enumeration and weightFiberCard its cardinality. finSuccFunctionEquiv appends a final coordinate, and weightPreimageEquiv identifies the weight preimage with its subtype. If n<=K, boundedPartitionTopEquiv forgets the vacuous upper bound and identifies bounded partitions with all partitions of n. Embedded lemmas prove the multiset, count and sum properties needed by these constructions. K=0 and n=0 remain in scope.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/EulerProduct.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

/-- The number of partitions of `n` all of whose parts are at most `K`. -/
noncomputable def partsLE (K n : ℕ) : ℕ :=
  Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}

/-- The weighted size of a multiplicity vector for parts `1, ..., K`. -/
def multiplicityWeight (K : ℕ) (q : Fin K → ℕ) : ℕ :=
  ∑ i : Fin K, (i.1 + 1) * q i

def countsMultiset {K : ℕ} (q : Fin K → ℕ) : Multiset ℕ :=
  ∑ i : Fin K, Multiset.replicate (q i) (i.1 + 1)

lemma countsMultiset_sum {K : ℕ} (q : Fin K → ℕ) :
    (countsMultiset q).sum = multiplicityWeight K q := by
  simp [countsMultiset, multiplicityWeight, Multiset.sum_sum, Multiset.sum_replicate,
    mul_comm]

lemma countsMultiset_pos {K : ℕ} (q : Fin K → ℕ) {m : ℕ} :
    m ∈ countsMultiset q → 0 < m := by
  intro hm
  rw [countsMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmrep⟩
  rw [Multiset.mem_replicate] at hmrep
  rcases hmrep with ⟨_, rfl⟩
  exact Nat.succ_pos _

lemma countsMultiset_le {K : ℕ} (q : Fin K → ℕ) {m : ℕ} :
    m ∈ countsMultiset q → m ≤ K := by
  intro hm
  rw [countsMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmrep⟩
  rw [Multiset.mem_replicate] at hmrep
  rcases hmrep with ⟨_, rfl⟩
  exact i.2

lemma countsMultiset_count {K : ℕ} (q : Fin K → ℕ) (i : Fin K) :
    (countsMultiset q).count (i.1 + 1) = q i := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hji (Fin.ext h)
    simp [hval]
  · intro hi
    simp at hi

lemma countsMultiset_count_eq_zero_of_lt {K : ℕ} (q : Fin K → ℕ) {m : ℕ}
    (hmK : K < m) :
    (countsMultiset q).count m = 0 := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : i.1 + 1 ≠ m := by omega
  simp [Multiset.count_replicate, hne]

lemma countsMultiset_count_zero {K : ℕ} (q : Fin K → ℕ) :
    (countsMultiset q).count 0 = 0 := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [Multiset.count_replicate]

noncomputable def partitionOfCountsAt {K n : ℕ}
    (q : {q : Fin K → ℕ // multiplicityWeight K q = n}) : Nat.Partition n where
  parts := countsMultiset q.1
  parts_pos := by
    intro _i hi
    exact countsMultiset_pos q.1 hi
  parts_sum := by
    rw [countsMultiset_sum, q.2]

lemma sum_fin_succ_eq_Icc {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℕ → M) :
    (∑ i : Fin K, f (i.1 + 1)) = ∑ k ∈ Finset.Icc 1 K, f k := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_bij (fun i _hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_pos i, Finset.mem_range.mp hi⟩
  · intro _a _ha _b _hb h
    exact Nat.succ.inj h
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Nat.sub_add_cancel hb.1
  · intro i hi
    have hlt : i < K := Finset.mem_range.mp hi
    simp [hlt]

lemma bounded_partition_count_sum {K n : ℕ} (p : Nat.Partition n)
    (hp : ∀ m ∈ p.parts, m ≤ K) :
    multiplicityWeight K (fun i : Fin K => p.parts.count (i.1 + 1)) = n := by
  classical
  have hIcc :
      (∑ m ∈ Finset.Icc 1 K, p.parts.count m * m) = n := by
    have hsupport : p.parts.toFinset ⊆ Finset.Icc 1 K := by
      intro m hm
      rw [Finset.mem_Icc]
      exact ⟨p.parts_pos (by simpa using hm), hp m (by simpa using hm)⟩
    convert ← p.parts_sum
    rw [Finset.sum_multiset_count]
    apply Finset.sum_subset hsupport
    intro x _hx hxnot
    simp [Multiset.count_eq_zero_of_notMem (by simpa using hxnot)]
  dsimp [multiplicityWeight]
  rw [sum_fin_succ_eq_Icc K (fun m => m * p.parts.count m)]
  simpa [Nat.mul_comm] using hIcc

noncomputable def boundedPartitionEquivCounts (K n : ℕ) :
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} ≃
      {q : Fin K → ℕ // multiplicityWeight K q = n} where
  toFun p := ⟨fun i => p.1.parts.count (i.1 + 1), bounded_partition_count_sum p.1 p.2⟩
  invFun q := ⟨partitionOfCountsAt q, by
    intro _m hm
    exact countsMultiset_le q.1 hm⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro m
    change Multiset.count m (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1))) =
      Multiset.count m p.1.parts
    by_cases hm0 : m = 0
    · subst hm0
      rw [countsMultiset_count_zero]
      have hp0 : 0 ∉ p.1.parts := by
        intro h
        exact (Nat.not_lt_zero _) (p.1.parts_pos h)
      simp [Multiset.count_eq_zero_of_notMem hp0]
    · have hmpos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
      by_cases hmK : m ≤ K
      · let i : Fin K := ⟨m - 1, by omega⟩
        have hi : i.1 + 1 = m := by dsimp [i]; omega
        calc
          Multiset.count m (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1)))
              = Multiset.count (i.1 + 1)
                  (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1))) := by rw [hi]
          _ = p.1.parts.count (i.1 + 1) := countsMultiset_count _ i
          _ = p.1.parts.count m := by rw [hi]
      · have hKlt : K < m := Nat.lt_of_not_ge hmK
        rw [countsMultiset_count_eq_zero_of_lt _ hKlt]
        have hnot : m ∉ p.1.parts := by
          intro hpmem
          exact (not_le_of_gt hKlt) (p.2 m hpmem)
        simp [Multiset.count_eq_zero_of_notMem hnot]
  right_inv := by
    intro q
    apply Subtype.ext
    funext i
    exact countsMultiset_count q.1 i

@[reducible]
noncomputable def weightFiberFintype (K n : ℕ) :
    Fintype {q : Fin K → ℕ // multiplicityWeight K q = n} :=
  Fintype.ofEquiv {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}
    (boundedPartitionEquivCounts K n)

noncomputable def weightFiberCard (K n : ℕ) : ℕ :=
  @Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n}
    (weightFiberFintype K n)

def finSuccFunctionEquiv (K : ℕ) : ((Fin K → ℕ) × ℕ) ≃ (Fin (K + 1) → ℕ) where
  toFun z := Fin.snoc z.1 z.2
  invFun q := (Fin.init q, q (Fin.last K))
  left_inv := by
    intro z
    ext i <;> simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := by
    intro q
    exact Fin.snoc_init_self q

def weightPreimageEquiv (K n : ℕ) :
    ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) ≃
      {q : Fin K → ℕ // multiplicityWeight K q = n} where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv := by intro b; rfl
  right_inv := by intro b; rfl

noncomputable def boundedPartitionTopEquiv (K n : ℕ) (h : n ≤ K) :
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} ≃ Nat.Partition n where
  toFun p := p.1
  invFun p := ⟨p, by
    intro _m hm
    exact (Nat.Partition.le_of_mem_parts hm).trans h⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

end AnalyticCombinatorics.Ch8.Partitions


