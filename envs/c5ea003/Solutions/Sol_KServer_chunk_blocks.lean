-- Prove2me | solution 1 for KServer.chunk_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T23:48:01.364972+00:00
-- url     : https://prove2.me/submissions/fe8f8b60-47dc-4168-bc7c-d1c753879ba3

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_race_var3

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace Blocks

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}

section Setup

variable (C : ChunkSystemB X s t cA cB T pe mL) (b : ℕ)

/-- Deterministic block boundaries. -/
def bIdx (k : ℕ) : ℕ := min (k * b) C.m

/-- The mass of block `k`. -/
noncomputable def bm (k : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.Ico (bIdx C b k) (bIdx C b (k + 1)), C.sizeN i ω

/-- Output size: the conditional block mass at the block start. -/
noncomputable def bsize (k : ℕ) (ω : C.Ω) : ℝ :=
  C.condExp (bm C b k) (bIdx C b k) ω

/-- Output chunk: the input chunks of one block, concatenated. -/
noncomputable def bchunk (ω : C.Ω) (k : ℕ) : List (Set X) :=
  (((List.ofFn (C.chunk ω)).take (bIdx C b (k + 1))).drop (bIdx C b k)).flatten

/-- The correction of block `k`: mass minus its conditional expectation. -/
noncomputable def corr (k : ℕ) (ω : C.Ω) : ℝ := bm C b k ω - bsize C b k ω

/-- Output total. -/
noncomputable def btotal (M : ℕ) (ω : C.Ω) : ℝ :=
  ∑ k ∈ Finset.range M, bsize C b k ω

/-- The below-floor count within block `k`. -/
noncomputable def badcnt (flo : ℝ) (k : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.Ico (bIdx C b k) (bIdx C b (k + 1)),
    if C.sizeN i ω < flo then (1 : ℝ) else 0

end Setup

section Idx

variable {C : ChunkSystemB X s t cA cB T pe mL} {b M : ℕ}

theorem bIdx_zero (C : ChunkSystemB X s t cA cB T pe mL) (b : ℕ) :
    bIdx C b 0 = 0 := by
  unfold bIdx
  omega

theorem bIdx_le_m (C : ChunkSystemB X s t cA cB T pe mL) (b k : ℕ) :
    bIdx C b k ≤ C.m := min_le_right _ _

theorem bIdx_mono (C : ChunkSystemB X s t cA cB T pe mL) (b : ℕ)
    {k k' : ℕ} (h : k ≤ k') : bIdx C b k ≤ bIdx C b k' := by
  have h1 : k * b ≤ k' * b := Nat.mul_le_mul h le_rfl
  unfold bIdx
  omega

theorem bIdx_last (hcov : C.m ≤ M * b) : bIdx C b M = C.m :=
  min_eq_right hcov

theorem bIdx_eq (hlastblk : (M - 1) * b < C.m) {k : ℕ} (hk : k < M) :
    bIdx C b k = k * b := by
  have h1 : k * b ≤ (M - 1) * b := Nat.mul_le_mul (by omega) le_rfl
  unfold bIdx
  omega

theorem blockLen_le (hlastblk : (M - 1) * b < C.m) {k : ℕ} (hk : k < M) :
    bIdx C b (k + 1) - bIdx C b k ≤ b := by
  have h1 : bIdx C b k = k * b := bIdx_eq hlastblk hk
  have h2 : bIdx C b (k + 1) ≤ (k + 1) * b := min_le_left _ _
  have h3 : (k + 1) * b = k * b + b := by ring
  omega

end Idx

section Congr

variable {C : ChunkSystemB X s t cA cB T pe mL}

theorem chunk_agree3 {n : ℕ} {ω ω' : C.Ω} (hh : C.hist n ω = C.hist n ω')
    {j : Fin C.m} (hj : (j : ℕ) < n) : C.chunk ω j = C.chunk ω' j :=
  C.hadapt j ω ω' (C.href ((j : ℕ) + 1) n (by omega) ω ω' hh)

theorem take_ofFn_agree {n : ℕ} {ω ω' : C.Ω} (hh : C.hist n ω = C.hist n ω') :
    (List.ofFn (C.chunk ω)).take n = (List.ofFn (C.chunk ω')).take n := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    have hkb : k < n := by
      simp only [List.length_take, List.length_ofFn] at h1
      omega
    exact chunk_agree3 hh hkb

end Congr

section OutputLemmas

variable {C : ChunkSystemB X s t cA cB T pe mL} {b M : ℕ}

theorem bm_congr {k : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (bIdx C b (k + 1)) ω' = C.hist (bIdx C b (k + 1)) ω) :
    bm C b k ω' = bm C b k ω := by
  unfold bm
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  exact C.sizeN_congr (C.href i (bIdx C b (k + 1)) (by omega) ω' ω hh)

theorem bsize_congr {k : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (bIdx C b k) ω' = C.hist (bIdx C b k) ω) :
    bsize C b k ω' = bsize C b k ω :=
  C.condExp_congr _ hh

theorem corr_congr {k : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (bIdx C b (k + 1)) ω' = C.hist (bIdx C b (k + 1)) ω) :
    corr C b k ω' = corr C b k ω := by
  unfold corr
  rw [bm_congr hh,
    bsize_congr (C.href (bIdx C b k) (bIdx C b (k + 1))
      (bIdx_mono C b (Nat.le_succ k)) ω' ω hh)]

theorem bchunk_congr {k : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (bIdx C b (k + 1)) ω = C.hist (bIdx C b (k + 1)) ω') :
    bchunk C b ω k = bchunk C b ω' k := by
  unfold bchunk
  rw [take_ofFn_agree hh]

/-- Blocks partition the input sequence. -/
theorem bchunk_prefix (ω : C.Ω) (i : ℕ) (hi : i ≤ M) :
    ((List.ofFn (fun k : Fin M => bchunk C b ω (k : ℕ))).take i).flatten
      = ((List.ofFn (C.chunk ω)).take (bIdx C b i)).flatten := by
  induction i with
  | zero =>
    rw [bIdx_zero]
    simp
  | succ i ih =>
    have hiM : i < M := by omega
    have htake : (List.ofFn (fun k : Fin M => bchunk C b ω (k : ℕ))).take (i + 1)
        = (List.ofFn (fun k : Fin M => bchunk C b ω (k : ℕ))).take i
          ++ [bchunk C b ω i] := by
      rw [List.take_succ]
      congr 1
      rw [List.getElem?_eq_getElem (by simp [hiM])]
      simp only [List.getElem_ofFn]
      rfl
    rw [htake, List.flatten_append, ih (by omega)]
    unfold bchunk
    rw [List.flatten_cons, List.flatten_nil, List.append_nil]
    have hτi : bIdx C b i ≤ bIdx C b (i + 1) := bIdx_mono C b (Nat.le_succ i)
    rw [← List.flatten_append]
    congr 1
    have hsplit := List.take_append_drop (bIdx C b i)
      ((List.ofFn (C.chunk ω)).take (bIdx C b (i + 1)))
    rw [List.take_take, min_eq_left hτi] at hsplit
    exact hsplit

theorem bchunk_flatten (hcov : C.m ≤ M * b) (ω : C.Ω) :
    (List.ofFn (fun k : Fin M => bchunk C b ω (k : ℕ))).flatten
      = (List.ofFn (C.chunk ω)).flatten := by
  have h1 := bchunk_prefix (C := C) (b := b) (M := M) ω M (le_refl M)
  rw [List.take_of_length_le (by simp)] at h1
  rw [bIdx_last hcov, List.take_of_length_le (by simp)] at h1
  exact h1

theorem bchunk_ne (ω : C.Ω) (k : ℕ) : ∀ S ∈ bchunk C b ω k, S.Nonempty := by
  intro S hS
  unfold bchunk at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (C.chunk ω) :=
    List.mem_of_mem_take (List.mem_of_mem_drop hl)
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hl2
  refine C.hne ω j S ?_
  rw [hj]
  exact hSl

theorem bm_nonneg (hcA0 : 0 ≤ cA) (k : ℕ) (ω : C.Ω) : 0 ≤ bm C b k ω :=
  Finset.sum_nonneg fun i _ => C.sizeN_nonneg hcA0 i ω

theorem bm_le (hcB0 : 0 ≤ cB) (hlastblk : (M - 1) * b < C.m)
    {k : ℕ} (hk : k < M) (ω : C.Ω) : bm C b k ω ≤ (b : ℝ) * cB := by
  have hsum : bm C b k ω
      ≤ ∑ _i ∈ Finset.Ico (bIdx C b k) (bIdx C b (k + 1)), cB := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    exact C.sizeN_le (lt_of_lt_of_le hi.2 (bIdx_le_m C b (k + 1))) ω
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hlen : bIdx C b (k + 1) - bIdx C b k ≤ b := blockLen_le hlastblk hk
  have hcast : ((bIdx C b (k + 1) - bIdx C b k : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hlen
  have h2 : ((bIdx C b (k + 1) - bIdx C b k : ℕ) : ℝ) * cB ≤ (b : ℝ) * cB :=
    mul_le_mul_of_nonneg_right hcast hcB0
  linarith

theorem bsize_nonneg (hcA0 : 0 ≤ cA) (k : ℕ) (ω : C.Ω) :
    0 ≤ bsize C b k ω :=
  C.le_condExp fun ω' _ => bm_nonneg hcA0 k ω'

theorem bsize_le (hcB0 : 0 ≤ cB) (hlastblk : (M - 1) * b < C.m)
    {k : ℕ} (hk : k < M) (ω : C.Ω) : bsize C b k ω ≤ (b : ℝ) * cB :=
  C.condExp_le fun ω' _ => bm_le hcB0 hlastblk hk ω'

/-- Grouped sums over the blocks recombine to a range sum. -/
theorem sum_range_blocks (C : ChunkSystemB X s t cA cB T pe mL) (b : ℕ)
    (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        ∑ i ∈ Finset.Ico (bIdx C b k) (bIdx C b (k + 1)), f i
      = ∑ i ∈ Finset.range (bIdx C b n), f i := by
  induction n with
  | zero =>
    rw [bIdx_zero]
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive f (Nat.zero_le _)
        (bIdx_mono C b (Nat.le_succ n))]

/-- The block masses recombine to the total. -/
theorem sum_bm (hcov : C.m ≤ M * b) (ω : C.Ω) :
    ∑ k ∈ Finset.range M, bm C b k ω = C.totalSize ω := by
  unfold bm
  rw [sum_range_blocks C b (fun i => C.sizeN i ω) M, bIdx_last hcov,
    ← Fin.sum_univ_eq_sum_range (fun i => C.sizeN i ω) C.m]
  unfold ChunkSystemB.totalSize
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos i.isLt]

end OutputLemmas

section CondLemmas

variable {C : ChunkSystemB X s t cA cB T pe mL} {b M : ℕ}

/-- The conditional expectation of a time-`h` measurable function is the
function itself. -/
theorem condExp_of_meas {f : C.Ω → ℝ} {h : ℕ} {ω : C.Ω}
    (hf : ∀ ω', C.hist h ω' = C.hist h ω → f ω' = f ω) :
    C.condExp f h ω = f ω := by
  unfold ChunkSystemB.condExp
  have h1 : ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      = f ω * C.mass (C.atom h ω) := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' hm => ?_
    rw [hf ω' (C.mem_atom.mp hm)]
    ring
  rw [h1, mul_div_assoc, div_self (ne_of_gt (C.mass_atom_pos h ω)), mul_one]

/-- Conditional expectations commute with finite sums. -/
theorem condExp_finset_sum {ι : Type*} (sset : Finset ι) (F : ι → C.Ω → ℝ)
    (h : ℕ) (ω : C.Ω) :
    C.condExp (fun ω' => ∑ i ∈ sset, F i ω') h ω
      = ∑ i ∈ sset, C.condExp (F i) h ω := by
  unfold ChunkSystemB.condExp
  rw [← Finset.sum_div]
  congr 1
  calc ∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i ∈ sset, F i ω'
      = ∑ ω' ∈ C.atom h ω, ∑ i ∈ sset, C.P ω' * F i ω' :=
        Finset.sum_congr rfl fun ω' _ => by rw [Finset.mul_sum]
    _ = ∑ i ∈ sset, ∑ ω' ∈ C.atom h ω, C.P ω' * F i ω' := Finset.sum_comm

/-- Corrections are conditionally centred at the block start. -/
theorem condExp_corr_zero (k : ℕ) (ω : C.Ω) :
    C.condExp (corr C b k) (bIdx C b k) ω = 0 := by
  have h1 : C.condExp (corr C b k) (bIdx C b k) ω
      = C.condExp (bm C b k) (bIdx C b k) ω
        - C.condExp (bsize C b k) (bIdx C b k) ω :=
    C.condExp_sub (bm C b k) (bsize C b k) (bIdx C b k) ω
  rw [h1]
  have h2 : C.condExp (bsize C b k) (bIdx C b k) ω = bsize C b k ω :=
    condExp_of_meas fun ω' hh => bsize_congr hh
  have h3 : C.condExp (bm C b k) (bIdx C b k) ω = bsize C b k ω := rfl
  rw [h2, h3, sub_self]

/-- Corrections stay centred at any earlier boundary. -/
theorem condExp_corr_deep {n k : ℕ} (hnk : n ≤ k) (ω : C.Ω) :
    C.condExp (corr C b k) (bIdx C b n) ω = 0 := by
  have h1 := C.condExp_condExp (f := corr C b k) (bIdx_mono C b hnk) ω
  rw [← h1,
    C.condExp_congr_fun (g := fun _ => (0 : ℝ))
      (fun ω' _ => condExp_corr_zero k ω')]
  exact C.condExp_const 0 _ ω

/-- **Orthogonality**: block corrections have additive second moments. -/
theorem sq_sum_corr (N : ℕ) :
    ∑ ω, C.P ω * (∑ k ∈ Finset.range N, corr C b k ω) ^ 2
      = ∑ k ∈ Finset.range N, ∑ ω, C.P ω * corr C b k ω ^ 2 := by
  have hcross : ∀ k k', k < k' →
      ∑ ω, C.P ω * (corr C b k ω * corr C b k' ω) = 0 := by
    intro k k' hlt
    have hu : ∀ ω ω' : C.Ω, C.hist (bIdx C b k') ω' = C.hist (bIdx C b k') ω →
        corr C b k ω' = corr C b k ω := fun ω ω' hh =>
      corr_congr (C.href (bIdx C b (k + 1)) (bIdx C b k')
        (bIdx_mono C b (by omega)) ω' ω hh)
    rw [ChunkSystemB.sum_P_mul_condExp (bIdx C b k') (corr C b k)
      (corr C b k') hu]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [condExp_corr_zero k' ω, mul_zero, mul_zero]
  have hexp : ∑ ω, C.P ω * (∑ k ∈ Finset.range N, corr C b k ω) ^ 2
      = ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ∑ ω, C.P ω * (corr C b k ω * corr C b k' ω) := by
    have h1 : ∀ ω : C.Ω, C.P ω * (∑ k ∈ Finset.range N, corr C b k ω) ^ 2
        = ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
            C.P ω * (corr C b k ω * corr C b k' ω) := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hexp]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [pow_two]
  · intro k' hk' hne
    rcases Nat.lt_or_ge k k' with h | h
    · exact hcross k k' h
    · have h' : k' < k := by omega
      rw [← hcross k' k h']
      exact Finset.sum_congr rfl fun ω _ => by ring
  · intro hc
    exact absurd (Finset.mem_range.mpr hk) hc

theorem sq_sum_corr_le_of {CV : ℝ} {N M' : ℕ} (hN : N ≤ M')
    (hCV' : ∑ k ∈ Finset.range M', ∑ ω, C.P ω * corr C b k ω ^ 2 ≤ CV) :
    ∑ ω, C.P ω * (∑ k ∈ Finset.range N, corr C b k ω) ^ 2 ≤ CV := by
  rw [sq_sum_corr N]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega) fun k _ _ =>
      Finset.sum_nonneg fun ω _ =>
        mul_nonneg (le_of_lt (C.hP ω)) (sq_nonneg _)) hCV'

/-- The output total is the input total minus the summed corrections. -/
theorem btotal_eq (hcov : C.m ≤ M * b) (ω : C.Ω) :
    btotal C b M ω = C.totalSize ω - ∑ k ∈ Finset.range M, corr C b k ω := by
  have h1 : ∑ k ∈ Finset.range M, corr C b k ω
      = (∑ k ∈ Finset.range M, bm C b k ω)
        - ∑ k ∈ Finset.range M, bsize C b k ω := by
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [h1, sum_bm hcov ω]
  unfold btotal
  ring

/-- Tower: the expected output total equals the expected input total. -/
theorem sum_btotal (hcov : C.m ≤ M * b) :
    ∑ ω, C.P ω * btotal C b M ω = ∑ ω, C.P ω * C.totalSize ω := by
  unfold btotal
  rw [Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum], Finset.sum_comm]
  have h1 : ∀ k ∈ Finset.range M, (∑ ω, C.P ω * bsize C b k ω)
      = ∑ ω, C.P ω * bm C b k ω :=
    fun k _ => C.sum_mul_condExp (bm C b k) (bIdx C b k)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← Finset.mul_sum, sum_bm hcov ω]

/-- The conditional summed correction at boundary `n` keeps only the
completed blocks. -/
theorem condExp_sum_corr {n : ℕ} (hnM : n ≤ M) (ω : C.Ω) :
    C.condExp (fun ω' => ∑ k ∈ Finset.range M, corr C b k ω')
        (bIdx C b n) ω
      = ∑ k ∈ Finset.range n, corr C b k ω := by
  rw [condExp_finset_sum]
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive
    (fun k => C.condExp (corr C b k) (bIdx C b n) ω) (Nat.zero_le n) hnM,
    ← Finset.range_eq_Ico]
  have h1 : ∑ k ∈ Finset.range n, C.condExp (corr C b k) (bIdx C b n) ω
      = ∑ k ∈ Finset.range n, corr C b k ω := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    refine condExp_of_meas fun ω' hh => ?_
    exact corr_congr (C.href (bIdx C b (k + 1)) (bIdx C b n)
      (bIdx_mono C b (by omega)) ω' ω hh)
  have h2 : ∑ k ∈ Finset.Ico n M, C.condExp (corr C b k) (bIdx C b n) ω
      = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_Ico] at hk
    exact condExp_corr_deep hk.1 ω
  rw [h1, h2, add_zero]

/-- Decomposition of the conditional output total. -/
theorem condExp_btotal (hcov : C.m ≤ M * b) {n : ℕ} (hnM : n ≤ M)
    (ω : C.Ω) :
    C.condExp (btotal C b M) (bIdx C b n) ω
      = C.condExp C.totalSize (bIdx C b n) ω
        - ∑ k ∈ Finset.range n, corr C b k ω := by
  have h1 : C.condExp (btotal C b M) (bIdx C b n) ω
      = C.condExp (fun ω' => C.totalSize ω'
          - ∑ k ∈ Finset.range M, corr C b k ω') (bIdx C b n) ω :=
    C.condExp_congr_fun fun ω' _ => btotal_eq hcov ω'
  rw [h1, C.condExp_sub, condExp_sum_corr hnM ω]

theorem max_add_abs (x y : ℝ) : max (x + y) 0 ≤ max x 0 + |y| := by
  refine max_le ?_ (add_nonneg (le_max_right x 0) (abs_nonneg y))
  have h1 : x ≤ max x 0 := le_max_left x 0
  have h2 : y ≤ |y| := le_abs_self y
  linarith

end CondLemmas

section Charge

variable {C : ChunkSystemB X s t cA cB T pe mL} {b M : ℕ}

/-- Inequality version of the saturated-set summation engine. -/
theorem sum_saturated_le' (h : ℕ) (Bs : Finset C.Ω)
    (hsat : ∀ ω ∈ Bs, ∀ ω', C.hist h ω' = C.hist h ω → ω' ∈ Bs)
    (f g : C.Ω → ℝ)
    (hfg : ∀ ω ∈ Bs, ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * g ω') :
    ∑ ω ∈ Bs, C.P ω * f ω ≤ ∑ ω ∈ Bs, C.P ω * g ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := Bs) (t := Bs.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * f ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := Bs) (t := Bs.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * g ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨ω₁, hω₁, hv1⟩ := Finset.mem_image.mp hv
  have hfiber : Bs.filter (fun ω => C.hist h ω = v) = C.atom h ω₁ := by
    ext ω
    simp only [Finset.mem_filter, C.mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hv1]
    · intro hω
      exact ⟨hsat ω₁ hω₁ ω hω, by rw [hω, hv1]⟩
  rw [hfiber]
  exact hfg ω₁ hω₁

/-- The bail-aware cost of the rest of block `k` from input position `j`. -/
noncomputable def bcost (C : ChunkSystemB X s t cA cB T pe mL) (b : ℕ)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (p' : ℝ) (k j : ℕ) (ω : C.Ω) : ℝ :=
  E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
    ((((List.ofFn (C.chunk ω)).take (bIdx C b (k + 1))).drop j).flatten) p'

theorem take_flatten_succ3 (ω : C.Ω) {j : ℕ} (hj : j < C.m) :
    ((List.ofFn (C.chunk ω)).take (j + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take j).flatten ++ C.chunk ω ⟨j, hj⟩ := by
  have h1 : (List.ofFn (C.chunk ω)).take (j + 1)
      = (List.ofFn (C.chunk ω)).take j ++ [C.chunk ω ⟨j, hj⟩] := by
    rw [List.take_succ]
    congr 1
    rw [List.getElem?_eq_getElem (by simp [hj])]
    simp only [List.getElem_ofFn]
    rfl
  rw [h1, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem block_cons (ω : C.Ω) {k j : ℕ} (hj : j < bIdx C b (k + 1)) :
    (((List.ofFn (C.chunk ω)).take (bIdx C b (k + 1))).drop j)
      = C.chunk ω ⟨j, lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))⟩
        :: (((List.ofFn (C.chunk ω)).take (bIdx C b (k + 1))).drop (j + 1)) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))
  have hlen : j < ((List.ofFn (C.chunk ω)).take (bIdx C b (k + 1))).length := by
    simp only [List.length_take, List.length_ofFn]
    omega
  rw [List.drop_eq_getElem_cons hlen]
  congr 1
  rw [List.getElem_take, List.getElem_ofFn]

theorem bcost_step_no_bail
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j : ℕ} (ω : C.Ω) (hj : j < bIdx C b (k + 1))
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))⟩) = none) :
    bcost C b E bail p' k j ω
      = E.costOn (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))⟩)
        + bcost C b E bail p' k (j + 1) ω := by
  have hjm : j < C.m := lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))
  unfold bcost
  rw [block_cons ω hj, List.flatten_cons,
    E.bailCost_append_of_no_bail bail _ _ _ _ hbail,
    ← take_flatten_succ3 ω hjm]

theorem bcost_step_bail
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j q : ℕ} (ω : C.Ω) (hj : j < bIdx C b (k + 1))
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))⟩) = some q) :
    bcost C b E bail p' k j ω
      = E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))⟩) pe
        + (p' - pe) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (bIdx_le_m C b (k + 1))
  unfold bcost
  rw [block_cons ω hj, List.flatten_cons,
    E.bailCost_append_of_bail bail _ _ _ _ hbail,
    E.bailCost_price_of_bail bail _ _ pe p' hbail]

theorem bcost_nonneg (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {p' : ℝ} (hp' : 0 ≤ p') (k j : ℕ) (ω : C.Ω) :
    0 ≤ bcost C b E bail p' k j ω :=
  E.bailCost_nonneg bail _ _ hp'

/-- The bail rule is quiet on all complete input chunks in `[a, j)`. -/
def quietB (bail : List (Set X) → Bool) (a j : ℕ) (ω : C.Ω) : Prop :=
  ∀ k, a ≤ k → k < j → ∀ hk : k < C.m,
    bailTime bail (((List.ofFn (C.chunk ω)).take k).flatten)
      (C.chunk ω ⟨k, hk⟩) = none

open Classical in
/-- The charging induction: remaining block mass is dominated by the
bail-aware cost, with escapes financed pointwise. -/
theorem charge_blk (hlastblk : (M - 1) * b < C.m)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    {p' : ℝ} (hp : pe + (b : ℝ) * cB ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    ∀ d j, bIdx C b k ≤ j → bIdx C b (k + 1) ≤ j + d →
    ∑ ω ∈ (C.atom (bIdx C b k) ω₀).filter
        (fun ω => quietB bail (bIdx C b k) j ω),
      C.P ω * (∑ i ∈ Finset.Ico j (bIdx C b (k + 1)), C.sizeN i ω)
    ≤ ∑ ω ∈ (C.atom (bIdx C b k) ω₀).filter
        (fun ω => quietB bail (bIdx C b k) j ω),
      C.P ω * bcost C b E bail p' k j ω := by
  have hbcB : (0 : ℝ) ≤ (b : ℝ) * cB := by positivity
  have hp0 : 0 ≤ p' := by linarith
  intro d
  induction d with
  | zero =>
    intro j haj hjd
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [show Finset.Ico j (bIdx C b (k + 1)) = ∅ from
      Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]
    exact mul_nonneg (le_of_lt (C.hP ω)) (bcost_nonneg E bail hp0 k j ω)
  | succ d ih =>
    intro j haj hjd
    by_cases hend : bIdx C b (k + 1) ≤ j
    · refine Finset.sum_le_sum fun ω _ => ?_
      rw [show Finset.Ico j (bIdx C b (k + 1)) = ∅ from
        Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]
      exact mul_nonneg (le_of_lt (C.hP ω)) (bcost_nonneg E bail hp0 k j ω)
    · push_neg at hend
      have hjm : j < C.m := lt_of_lt_of_le hend (bIdx_le_m C b (k + 1))
      set a := bIdx C b k with ha_def
      set NBW := (C.atom a ω₀).filter (fun ω => quietB bail a j ω)
        with hNBW_def
      have hsat_NBW : ∀ ω ∈ NBW, ∀ ω', C.hist j ω' = C.hist j ω →
          ω' ∈ NBW := by
        intro ω hm ω' hh
        rw [hNBW_def, Finset.mem_filter] at hm ⊢
        refine ⟨?_, ?_⟩
        · rw [C.mem_atom]
          exact (C.href a j haj ω' ω hh).trans (C.mem_atom.mp hm.1)
        · intro i hai hij hi
          have hhk : C.hist i ω' = C.hist i ω := C.href i j (by omega) ω' ω hh
          have hhk1 : C.hist (i + 1) ω' = C.hist (i + 1) ω :=
            C.href (i + 1) j (by omega) ω' ω hh
          rw [take_ofFn_agree hhk, chunk_agree3 hhk1 (Nat.lt_succ_self i)]
          exact hm.2 i hai hij hi
      have hprem : ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
          ≤ ∑ ω ∈ NBW, C.P ω *
              E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe := by
        refine sum_saturated_le' j NBW hsat_NBW _ _
          fun ω₁ _ => ?_
        have hpre : C.size ω₁ ⟨j, hjm⟩ * C.mass (C.atom j ω₁)
            ≤ ∑ ω' ∈ C.atom j ω₁, C.P ω' *
                E.bailCost bail (((List.ofFn (C.chunk ω')).take j).flatten)
                  (C.chunk ω' ⟨j, hjm⟩) pe := C.hcost ⟨j, hjm⟩ ω₁ E bail
        refine le_trans (le_of_eq ?_) hpre
        unfold ChunkSystemB.mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω' hm' => ?_
        unfold ChunkSystemB.sizeN
        rw [dif_pos hjm, C.hsmeas ⟨j, hjm⟩ ω' ω₁ (C.mem_atom.mp hm')]
        ring
      set cond1 : C.Ω → Prop := fun ω =>
        bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, hjm⟩) = none with hcond1_def
      set S1 := NBW.filter cond1 with hS1_def
      set S3 := NBW.filter (fun ω => ¬ cond1 ω) with hS3_def
      have hS1_eq : S1 = (C.atom a ω₀).filter
          (fun ω => quietB bail a (j + 1) ω) := by
        rw [hS1_def, hNBW_def, Finset.filter_filter]
        ext ω
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hA, hq, hc1⟩
          refine ⟨hA, ?_⟩
          intro i hai hij hi
          rcases Nat.lt_or_ge i j with hij' | hij'
          · exact hq i hai hij' hi
          · have hieq : i = j := by omega
            subst hieq
            exact hc1
        · rintro ⟨hA, hq⟩
          have hc1 : cond1 ω := hq j haj (by omega) hjm
          exact ⟨hA, fun i hai hij hi => hq i hai (by omega) hi, hc1⟩
      have hsplit0 : ∀ f : C.Ω → ℝ, ∑ ω ∈ NBW, f ω
          = ∑ ω ∈ S1, f ω + ∑ ω ∈ S3, f ω := fun f =>
        (Finset.sum_filter_add_sum_filter_not NBW cond1 f).symm
      have hS1_mem : ∀ ω ∈ S1, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS1_def, Finset.mem_filter] at hm
        exact hm
      have hS3_mem : ∀ ω ∈ S3, ω ∈ NBW ∧ ¬ cond1 ω := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        exact hm
      have htail_le : ∀ ω : C.Ω,
          ∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω
            ≤ p' - pe := by
        intro ω
        have hlen : bIdx C b (k + 1) - bIdx C b k ≤ b :=
          blockLen_le hlastblk (by omega)
        have hsum : ∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω
            ≤ ∑ _i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), cB := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_Ico] at hi
          exact C.sizeN_le (lt_of_lt_of_le hi.2 (bIdx_le_m C b (k + 1))) ω
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
        have hcnt : bIdx C b (k + 1) - (j + 1) ≤ b := by omega
        have hcast : ((bIdx C b (k + 1) - (j + 1) : ℕ) : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast hcnt
        have h2 : ((bIdx C b (k + 1) - (j + 1) : ℕ) : ℝ) * cB
            ≤ (b : ℝ) * cB := mul_le_mul_of_nonneg_right hcast hcB0
        linarith
      have hcost_S1 : ∀ ω ∈ S1,
          C.P ω * bcost C b E bail p' k j ω
            = C.P ω * E.bailCost bail
                (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * bcost C b E bail p' k (j + 1) ω := by
        intro ω hm
        obtain ⟨_, hc⟩ := hS1_mem ω hm
        simp only [hcond1_def] at hc
        rw [bcost_step_no_bail E bail p' ω hend hc,
          E.bailCost_of_no_bail bail _ _ pe hc]
        ring
      have hcost_S3 : ∀ ω ∈ S3,
          C.P ω * bcost C b E bail p' k j ω
            = C.P ω * E.bailCost bail
                (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * (p' - pe) := by
        intro ω hm
        obtain ⟨_, hc⟩ := hS3_mem ω hm
        simp only [hcond1_def] at hc
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
        rw [bcost_step_bail E bail p' ω hend hq]
        ring
      have hLHS : ∑ ω ∈ NBW, C.P ω *
            (∑ i ∈ Finset.Ico j (bIdx C b (k + 1)), C.sizeN i ω)
          = ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
            + (∑ ω ∈ S1, C.P ω *
                (∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω)
              + ∑ ω ∈ S3, C.P ω *
                (∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω)) := by
        rw [Finset.sum_congr rfl fun ω _ => by
            rw [Finset.sum_eq_sum_Ico_succ_bot hend, mul_add],
          Finset.sum_add_distrib,
          hsplit0 (fun ω => C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω))]
      have hRHS : ∑ ω ∈ NBW, C.P ω * bcost C b E bail p' k j ω
          = ∑ ω ∈ NBW, C.P ω * E.bailCost bail
              (((List.ofFn (C.chunk ω)).take j).flatten)
              (C.chunk ω ⟨j, hjm⟩) pe
            + (∑ ω ∈ S1, C.P ω * bcost C b E bail p' k (j + 1) ω
              + ∑ ω ∈ S3, C.P ω * (p' - pe)) := by
        rw [hsplit0 (fun ω => C.P ω * bcost C b E bail p' k j ω),
          hsplit0 (fun ω => C.P ω * E.bailCost bail
            (((List.ofFn (C.chunk ω)).take j).flatten)
            (C.chunk ω ⟨j, hjm⟩) pe)]
        rw [Finset.sum_congr rfl hcost_S1, Finset.sum_congr rfl hcost_S3,
          Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
      rw [hLHS, hRHS]
      have hIH : ∑ ω ∈ S1, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω)
          ≤ ∑ ω ∈ S1, C.P ω * bcost C b E bail p' k (j + 1) ω := by
        rw [hS1_eq]
        exact ih (j + 1) (by omega) (by omega)
      have hS3_fin : ∑ ω ∈ S3, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (bIdx C b (k + 1)), C.sizeN i ω)
          ≤ ∑ ω ∈ S3, C.P ω * (p' - pe) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        exact mul_le_mul_of_nonneg_left (htail_le ω) (le_of_lt (C.hP ω))
      linarith [hprem, hIH, hS3_fin]

open Classical in
/-- The output conditional cost bound, over the block-start atom. -/
theorem bcost_bound (hcov : C.m ≤ M * b) (hlastblk : (M - 1) * b < C.m)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    {p' : ℝ} (hp : pe + (b : ℝ) * cB ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    bsize C b k ω₀ * C.mass (C.atom (bIdx C b k) ω₀)
      ≤ ∑ ω ∈ C.atom (bIdx C b k) ω₀,
          C.P ω * E.bailCost bail
            (((List.ofFn (fun i : Fin M => bchunk C b ω (i : ℕ))).take k).flatten)
            (bchunk C b ω k) p' := by
  set a := bIdx C b k with ha_def
  have hL : bsize C b k ω₀ * C.mass (C.atom a ω₀)
      = ∑ ω ∈ C.atom a ω₀, C.P ω * bm C b k ω := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum, ← C.sum_atom_mul_condExp (bm C b k) a ω₀]
    refine Finset.sum_congr rfl fun ω hm => ?_
    have he : C.condExp (bm C b k) a ω = bsize C b k ω₀ := by
      have h1 : C.condExp (bm C b k) a ω = C.condExp (bm C b k) a ω₀ :=
        C.condExp_congr _ (C.mem_atom.mp hm)
      rw [h1]
      rfl
    rw [he]
    ring
  have hfull : (C.atom a ω₀).filter (fun ω => quietB bail a a ω)
      = C.atom a ω₀ := by
    rw [Finset.filter_eq_self]
    intro ω _ i hai hia hi
    exact absurd hia (by omega)
  have hclaim := charge_blk hlastblk hcA0 hcB0 hp hpe E bail hk ω₀
    C.m a (le_refl a) (by have := bIdx_le_m C b (k + 1); omega)
  rw [hfull] at hclaim
  have hR : ∀ ω ∈ C.atom a ω₀, bcost C b E bail p' k a ω
      = E.bailCost bail
          (((List.ofFn (fun i : Fin M => bchunk C b ω (i : ℕ))).take k).flatten)
          (bchunk C b ω k) p' := by
    intro ω _
    unfold bcost
    rw [bchunk_prefix (b := b) ω k (by omega)]
    rfl
  rw [hL]
  refine le_trans hclaim (le_of_eq ?_)
  exact Finset.sum_congr rfl fun ω hm => by rw [hR ω hm]

end Charge

section Markov

variable {C : ChunkSystemB X s t cA cB T pe mL} {b M : ℕ}

/-- **Conditional Markov step**: a block whose conditional mass falls below
`(1-θ)·b·flo` has conditional below-floor count above `θ·b`. -/
theorem markov_block (hcA0 : 0 ≤ cA) {flo θ : ℝ}
    (hflo : 0 < flo) (hθ : 0 < θ) (hlastblk : (M - 1) * b < C.m)
    {k : ℕ} (hk1 : k + 1 < M) (ω : C.Ω) :
    θ * (b : ℝ) * (if bsize C b k ω < (1 - θ) * ((b : ℝ) * flo)
        then (1 : ℝ) else 0)
      ≤ C.condExp (badcnt C b flo k) (bIdx C b k) ω := by
  have hbadnn : 0 ≤ C.condExp (badcnt C b flo k) (bIdx C b k) ω :=
    C.le_condExp fun ω' _ => Finset.sum_nonneg fun i _ => by positivity
  by_cases hbs : bsize C b k ω < (1 - θ) * ((b : ℝ) * flo)
  case neg =>
    rw [if_neg hbs, mul_zero]
    exact hbadnn
  rw [if_pos hbs, mul_one]
  have hak : bIdx C b k = k * b := bIdx_eq hlastblk (by omega)
  have hak1 : bIdx C b (k + 1) = (k + 1) * b := bIdx_eq hlastblk (by omega)
  have hcard : (Finset.Ico (bIdx C b k) (bIdx C b (k + 1))).card = b := by
    rw [Nat.card_Ico, hak, hak1]
    have h3 : (k + 1) * b = k * b + b := by ring
    omega
  have hbm_ge : ∀ ω' : C.Ω,
      flo * (b : ℝ) - badcnt C b flo k ω' * flo ≤ bm C b k ω' := by
    intro ω'
    have h1 : ∀ i ∈ Finset.Ico (bIdx C b k) (bIdx C b (k + 1)),
        flo - (if C.sizeN i ω' < flo then (1 : ℝ) else 0) * flo
          ≤ C.sizeN i ω' := by
      intro i _
      by_cases hs : C.sizeN i ω' < flo
      · rw [if_pos hs, one_mul]
        have := C.sizeN_nonneg hcA0 i ω'
        linarith
      · rw [if_neg hs, zero_mul, sub_zero]
        linarith [not_lt.mp hs]
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard,
      ← Finset.sum_mul, nsmul_eq_mul] at h2
    unfold bm badcnt
    have hbf : (b : ℝ) * flo = flo * (b : ℝ) := by ring
    linarith [h2]
  have hcond : flo * (b : ℝ)
      - C.condExp (badcnt C b flo k) (bIdx C b k) ω * flo
        ≤ bsize C b k ω := by
    have h3 : C.condExp (fun ω' => flo * (b : ℝ)
          - badcnt C b flo k ω' * flo) (bIdx C b k) ω
        ≤ C.condExp (bm C b k) (bIdx C b k) ω :=
      C.condExp_mono _ _ fun ω' _ => hbm_ge ω'
    have h4 : C.condExp (fun ω' => flo * (b : ℝ)
          - badcnt C b flo k ω' * flo) (bIdx C b k) ω
        = flo * (b : ℝ)
          - C.condExp (badcnt C b flo k) (bIdx C b k) ω * flo := by
      rw [C.condExp_sub (fun _ => flo * (b : ℝ))
        (fun ω' => badcnt C b flo k ω' * flo) (bIdx C b k) ω,
        C.condExp_const, C.condExp_mul_const]
    rw [h4] at h3
    exact h3
  set XB := C.condExp (badcnt C b flo k) (bIdx C b k) ω
  have h5 : θ * (b : ℝ) * flo < XB * flo := by nlinarith
  have h6 : θ * (b : ℝ) < XB := lt_of_mul_lt_mul_right h5 (le_of_lt hflo)
  exact le_of_lt h6

end Markov

section Assemble

variable {C : ChunkSystemB X s t cA cB T pe mL}

open Classical in
/-- **Fixed-block regrouping**: blocks of `b` consecutive chunks with
deterministic boundaries, sized by the conditional block mass at the
block start.  Preserves the expected total exactly; the output variance
is at most `2V + 2CV`; L¹-sturdiness passes through with a `√CV`
correction; the below-floor count resets by Markov. -/
theorem chunk_blocks (C : ChunkSystemB X s t cA cB T pe mL)
    {b M n₀ : ℕ} {p' V CV D B flo θ : ℝ}
    (hb0 : 0 < b) (hM0 : 0 < M) (hMm : M ≤ C.m)
    (hcov : C.m ≤ M * b) (hlastblk : (M - 1) * b < C.m)
    (hn₀M : n₀ + 1 ≤ M)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (b : ℝ) * cB ≤ p')
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hCV : ∑ k ∈ Finset.range M, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
            C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
              C.sizeN i ω') (min (k * b) C.m) ω) ^ 2 ≤ CV)
    (hCV0 : 0 ≤ CV)
    (hst : C.SturdyL1 (n₀ * b) D)
    (hbad : ∀ n ≤ n₀ * b, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hθ : 0 < θ) (hflo : 0 < flo) :
    ∃ C' : ChunkSystemB X s t 0 ((b : ℝ) * cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 2 * V + 2 * CV) ∧
      C'.SturdyL1 n₀ (D + Real.sqrt CV) ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))) := by
  have hCV' : ∑ k ∈ Finset.range M, ∑ ω, C.P ω * corr C b k ω ^ 2 ≤ CV := hCV
  have hVar' : ∑ ω, C.P ω * (C.totalSize ω
      - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 ≤ V := hVar
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := M
    hist := fun n ω => C.hist (bIdx C b n) ω
    chunk := fun ω k => bchunk C b ω (k : ℕ)
    size := fun ω k => bsize C b (k : ℕ) ω
    hP := C.hP
    hPsum := C.hPsum
    hm := le_refl M
    hm0 := hM0
    href := fun i j hij ω ω' hh =>
      C.href (bIdx C b i) (bIdx C b j) (bIdx_mono C b hij) ω ω' hh
    hadapt := fun k ω ω' hh => bchunk_congr hh
    hsmeas := fun k ω ω' hh => C.condExp_congr _ hh
    hne := fun ω k => bchunk_ne ω (k : ℕ)
    hlast := ?_
    hopt := ?_
    hsize := ?_
    hcost := ?_
    htotal := ?_ }, rfl, ?_, ?_, ?_, ?_⟩
  · intro ω
    rw [bchunk_flatten hcov ω]
    exact C.hlast ω
  · intro ω
    rw [bchunk_flatten hcov ω]
    exact C.hopt ω
  · intro ω k
    exact ⟨bsize_nonneg hcA0 (k : ℕ) ω, bsize_le hcB0 hlastblk k.isLt ω⟩
  · intro k ω₀ E bail
    exact bcost_bound hcov hlastblk hcA0 hcB0 hp hpe E bail k.isLt ω₀
  · -- total: exact preservation
    have h1 : ∑ ω, C.P ω * (∑ k : Fin M, bsize C b (k : ℕ) ω)
        = ∑ ω, C.P ω * btotal C b M ω := by
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Fin.sum_univ_eq_sum_range (fun k => bsize C b k ω) M]
      rfl
    rw [h1, sum_btotal hcov]
    exact C.htotal
  · -- trivial initial history
    intro ω₁ ω₂
    show C.hist (bIdx C b 0) ω₁ = C.hist (bIdx C b 0) ω₂
    rw [bIdx_zero]
    exact h0triv ω₁ ω₂
  · -- output variance
    show ∑ ω, C.P ω * ((∑ i : Fin M, bsize C b (i : ℕ) ω)
        - ∑ ω', C.P ω' * (∑ i : Fin M, bsize C b (i : ℕ) ω')) ^ 2
      ≤ 2 * V + 2 * CV
    have hfin : ∀ ω : C.Ω, (∑ i : Fin M, bsize C b (i : ℕ) ω)
        = btotal C b M ω := fun ω =>
      Fin.sum_univ_eq_sum_range (fun k => bsize C b k ω) M
    have hμ : (∑ ω', C.P ω' * (∑ i : Fin M, bsize C b (i : ℕ) ω'))
        = ∑ ω', C.P ω' * C.totalSize ω' := by
      rw [Finset.sum_congr rfl fun ω' _ => by rw [hfin ω']]
      exact sum_btotal hcov
    rw [hμ, Finset.sum_congr rfl fun ω _ => by rw [hfin ω]]
    set μ := ∑ ω', C.P ω' * C.totalSize ω' with hμ_def
    have hS2 : ∑ ω, C.P ω * (∑ k ∈ Finset.range M, corr C b k ω) ^ 2 ≤ CV :=
      sq_sum_corr_le_of (le_refl M) hCV'
    have hpt : ∀ ω : C.Ω, (btotal C b M ω - μ) ^ 2
        ≤ 2 * (C.totalSize ω - μ) ^ 2
          + 2 * (∑ k ∈ Finset.range M, corr C b k ω) ^ 2 := by
      intro ω
      rw [btotal_eq hcov ω]
      nlinarith [sq_nonneg ((C.totalSize ω - μ)
        + ∑ k ∈ Finset.range M, corr C b k ω)]
    calc ∑ ω, C.P ω * (btotal C b M ω - μ) ^ 2
        ≤ ∑ ω, C.P ω * (2 * (C.totalSize ω - μ) ^ 2
            + 2 * (∑ k ∈ Finset.range M, corr C b k ω) ^ 2) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hpt ω) (le_of_lt (C.hP ω))
      _ = 2 * (∑ ω, C.P ω * (C.totalSize ω - μ) ^ 2)
          + 2 * ∑ ω, C.P ω * (∑ k ∈ Finset.range M, corr C b k ω) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ 2 * V + 2 * CV := by linarith [hVar']
  · -- L¹-sturdiness passes through with a √CV correction
    intro n hn
    have hnM : n < M := by omega
    have hbn : bIdx C b n = n * b := bIdx_eq hlastblk hnM
    show ∑ ω, C.P ω * max ((∑ ω', C.P ω'
          * (∑ i : Fin M, bsize C b (i : ℕ) ω'))
        - C.condExp (fun ω' => ∑ i : Fin M, bsize C b (i : ℕ) ω')
            (bIdx C b n) ω) 0 ≤ D + Real.sqrt CV
    have htoteq : ∀ ω : C.Ω, (∑ i : Fin M, bsize C b (i : ℕ) ω)
        = btotal C b M ω := fun ω =>
      Fin.sum_univ_eq_sum_range (fun k => bsize C b k ω) M
    have hE : (∑ ω', C.P ω' * (∑ i : Fin M, bsize C b (i : ℕ) ω'))
        = C.expTotal := by
      rw [Finset.sum_congr rfl fun ω' _ => by rw [htoteq ω']]
      exact sum_btotal hcov
    have hce : ∀ ω : C.Ω,
        C.condExp (fun ω' => ∑ i : Fin M, bsize C b (i : ℕ) ω')
            (bIdx C b n) ω
          = C.condExp C.totalSize (bIdx C b n) ω
            - ∑ k ∈ Finset.range n, corr C b k ω := by
      intro ω
      rw [C.condExp_congr_fun fun ω' _ => htoteq ω']
      exact condExp_btotal hcov (le_of_lt hnM) ω
    have hpt : ∀ ω : C.Ω, max ((∑ ω', C.P ω'
          * (∑ i : Fin M, bsize C b (i : ℕ) ω'))
        - C.condExp (fun ω' => ∑ i : Fin M, bsize C b (i : ℕ) ω')
            (bIdx C b n) ω) 0
        ≤ max (C.expTotal - C.condExp C.totalSize (bIdx C b n) ω) 0
          + |∑ k ∈ Finset.range n, corr C b k ω| := by
      intro ω
      rw [hE, hce ω]
      have harg : C.expTotal - (C.condExp C.totalSize (bIdx C b n) ω
            - ∑ k ∈ Finset.range n, corr C b k ω)
          = (C.expTotal - C.condExp C.totalSize (bIdx C b n) ω)
            + ∑ k ∈ Finset.range n, corr C b k ω := by ring
      rw [harg]
      exact max_add_abs _ _
    calc ∑ ω, C.P ω * max ((∑ ω', C.P ω'
            * (∑ i : Fin M, bsize C b (i : ℕ) ω'))
          - C.condExp (fun ω' => ∑ i : Fin M, bsize C b (i : ℕ) ω')
              (bIdx C b n) ω) 0
        ≤ ∑ ω, C.P ω
            * (max (C.expTotal - C.condExp C.totalSize (bIdx C b n) ω) 0
              + |∑ k ∈ Finset.range n, corr C b k ω|) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hpt ω) (le_of_lt (C.hP ω))
      _ = (∑ ω, C.P ω
            * max (C.expTotal - C.condExp C.totalSize (bIdx C b n) ω) 0)
          + ∑ ω, C.P ω * |∑ k ∈ Finset.range n, corr C b k ω| := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ D + Real.sqrt CV := by
          refine add_le_add ?_ ?_
          · have h1 := hst (n * b) (Nat.mul_le_mul hn le_rfl)
            rw [hbn]
            exact h1
          · exact Race.sum_abs_le_sqrt C.P _
              (fun ω => le_of_lt (C.hP ω)) C.hPsum
              (sq_sum_corr_le_of (le_of_lt hnM) hCV')
  · -- below-floor block count by Markov
    intro n hn
    show ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if (if hh : i < M then bsize C b i ω else 0)
            < (1 - θ) * ((b : ℝ) * flo)
        then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))
    have hrw : ∀ ω : C.Ω, (∑ i ∈ Finset.range n,
          if (if hh : i < M then bsize C b i ω else 0)
              < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0)
        = ∑ i ∈ Finset.range n,
            if bsize C b i ω < (1 - θ) * ((b : ℝ) * flo)
            then (1 : ℝ) else 0 := by
      intro ω
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [dif_pos (show i < M by omega)]
    rw [Finset.sum_congr rfl fun ω _ => by rw [hrw ω]]
    have hb0R : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
    have hθb : (0 : ℝ) < θ * (b : ℝ) := mul_pos hθ hb0R
    rw [le_div_iff₀ hθb]
    have h1 : ∀ ω : C.Ω, (∑ i ∈ Finset.range n,
          if bsize C b i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) * (θ * (b : ℝ))
        ≤ ∑ k ∈ Finset.range n,
            C.condExp (badcnt C b flo k) (bIdx C b k) ω := by
      intro ω
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_range] at hk
      have h2 := markov_block hcA0 hflo hθ hlastblk
        (show k + 1 < M by omega) ω
      linarith [h2]
    have hmv : (∑ ω, C.P ω * (∑ i ∈ Finset.range n,
          if bsize C b i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0)) * (θ * (b : ℝ))
        = ∑ ω, C.P ω * ((∑ i ∈ Finset.range n,
            if bsize C b i ω < (1 - θ) * ((b : ℝ) * flo)
            then (1 : ℝ) else 0) * (θ * (b : ℝ))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [hmv]
    calc ∑ ω, C.P ω * ((∑ i ∈ Finset.range n,
            if bsize C b i ω < (1 - θ) * ((b : ℝ) * flo)
            then (1 : ℝ) else 0) * (θ * (b : ℝ)))
        ≤ ∑ ω, C.P ω * (∑ k ∈ Finset.range n,
            C.condExp (badcnt C b flo k) (bIdx C b k) ω) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (h1 ω) (le_of_lt (C.hP ω))
      _ = ∑ k ∈ Finset.range n, ∑ ω, C.P ω
            * C.condExp (badcnt C b flo k) (bIdx C b k) ω := by
          rw [Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]]
          exact Finset.sum_comm
      _ = ∑ k ∈ Finset.range n, ∑ ω, C.P ω * badcnt C b flo k ω :=
          Finset.sum_congr rfl fun k _ =>
            C.sum_mul_condExp (badcnt C b flo k) (bIdx C b k)
      _ = ∑ ω, C.P ω * ∑ k ∈ Finset.range n, badcnt C b flo k ω := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]
      _ = ∑ ω, C.P ω * (∑ i ∈ Finset.range (n * b),
            if C.sizeN i ω < flo then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          congr 1
          have h3 : ∑ k ∈ Finset.range n, badcnt C b flo k ω
              = ∑ i ∈ Finset.range (bIdx C b n),
                  if C.sizeN i ω < flo then (1 : ℝ) else 0 :=
            sum_range_blocks C b
              (fun i => if C.sizeN i ω < flo then (1 : ℝ) else 0) n
          rw [h3, bIdx_eq hlastblk (show n < M by omega)]
      _ ≤ B := hbad (n * b) (Nat.mul_le_mul hn le_rfl)

end Assemble

end Blocks

namespace KServer

/-- **Fixed-block regrouping**: group the `m` chunks of a chunk system into
`M` blocks of `b` consecutive chunks with deterministic boundaries
`min (k·b) m`; the output size of block `k` is the conditional block mass
at the block start.  The expected total is preserved exactly; the output
variance is at most `2V + 2CV` where `CV` bounds the summed conditional
block variances; L¹-sturdiness passes through with an additive `√CV`; and
the below-floor block count resets by Markov's inequality. -/
theorem chunk_blocks {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {b M n₀ : ℕ} {p' V CV D B flo θ : ℝ}
    (hb0 : 0 < b) (hM0 : 0 < M) (hMm : M ≤ C.m)
    (hcov : C.m ≤ M * b) (hlastblk : (M - 1) * b < C.m)
    (hn₀M : n₀ + 1 ≤ M)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (b : ℝ) * cB ≤ p')
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hCV : ∑ k ∈ Finset.range M, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
            C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
              C.sizeN i ω') (min (k * b) C.m) ω) ^ 2 ≤ CV)
    (hCV0 : 0 ≤ CV)
    (hst : C.SturdyL1 (n₀ * b) D)
    (hbad : ∀ n ≤ n₀ * b, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hθ : 0 < θ) (hflo : 0 < flo) :
    ∃ C' : ChunkSystemB X s t 0 ((b : ℝ) * cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 2 * V + 2 * CV) ∧
      C'.SturdyL1 n₀ (D + Real.sqrt CV) ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))) :=
  Blocks.chunk_blocks C hb0 hM0 hMm hcov hlastblk hn₀M hcA0 hcB0 hpe hp
    h0triv hVar hCV hCV0 hst hbad hθ hflo

end KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : KServer.ChunkSystemB X s t cA cB T pe mL)
    {b M n₀ : ℕ} {p' V CV D B flo θ : ℝ}
    (hb0 : 0 < b) (hM0 : 0 < M) (hMm : M ≤ C.m)
    (hcov : C.m ≤ M * b) (hlastblk : (M - 1) * b < C.m)
    (hn₀M : n₀ + 1 ≤ M)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (b : ℝ) * cB ≤ p')
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hCV : ∑ k ∈ Finset.range M, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
            C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
              C.sizeN i ω') (min (k * b) C.m) ω) ^ 2 ≤ CV)
    (hCV0 : 0 ≤ CV)
    (hst : C.SturdyL1 (n₀ * b) D)
    (hbad : ∀ n ≤ n₀ * b, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hθ : 0 < θ) (hflo : 0 < flo) :
    ∃ C' : KServer.ChunkSystemB X s t 0 ((b : ℝ) * cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 2 * V + 2 * CV) ∧
      C'.SturdyL1 n₀ (D + Real.sqrt CV) ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))) :=
  KServer.chunk_blocks C hb0 hM0 hMm hcov hlastblk hn₀M hcA0 hcB0 hpe hp
    h0triv hVar hCV hCV0 hst hbad hθ hflo
