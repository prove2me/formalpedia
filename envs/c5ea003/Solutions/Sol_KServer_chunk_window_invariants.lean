-- Prove2me | solution 1 for KServer.chunk_window_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T13:28:26.028002+00:00
-- url     : https://prove2.me/submissions/4817d5f5-5a12-4952-9e7c-655a11272849

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy

open KServer
open KServer.ChunkSystemB

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (n₀ : ℕ) (hn₀ : n₀ ≤ C.m) (flo : ℝ) (hflo : flo ≤ cLo) :
    C.SturdyL1 n₀ ((C.m : ℝ) * (cHi - cLo)) ∧
    C.DoobJumpBound ((C.m : ℝ) * (cHi - cLo)) ∧
    (∀ n ≤ n₀, ∑ ω, C.P ω *
      (∑ i ∈ Finset.range n, if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ 0) := by
  classical
  -- the sample space is nonempty
  have hne : Nonempty C.Ω := by
    by_contra h
    have hempty : (Finset.univ : Finset C.Ω) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun ω _ => h ⟨ω⟩
    have := C.hPsum
    rw [hempty, Finset.sum_empty] at this
    norm_num at this
  obtain ⟨ω₀⟩ := hne
  have hi₀ : (0 : ℕ) < C.m := C.hm0
  have hlo_hi : cLo ≤ cHi := by
    have h := C.hsize ω₀ ⟨0, hi₀⟩
    linarith [h.1, h.2]
  have hD0 : 0 ≤ (C.m : ℝ) * (cHi - cLo) := by
    have : (0 : ℝ) ≤ (C.m : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- pointwise bounds on the total size
  have htot_le : ∀ ω : C.Ω, C.totalSize ω ≤ (C.m : ℝ) * cHi := by
    intro ω
    have : ∑ i : Fin C.m, C.size ω i ≤ ∑ _i : Fin C.m, cHi :=
      Finset.sum_le_sum fun i _ => (C.hsize ω i).2
    simpa [ChunkSystemB.totalSize, Finset.sum_const, Finset.card_univ, mul_comm] using this
  have hle_tot : ∀ ω : C.Ω, (C.m : ℝ) * cLo ≤ C.totalSize ω := by
    intro ω
    have : ∑ _i : Fin C.m, cLo ≤ ∑ i : Fin C.m, C.size ω i :=
      Finset.sum_le_sum fun i _ => (C.hsize ω i).1
    simpa [ChunkSystemB.totalSize, Finset.sum_const, Finset.card_univ, mul_comm] using this
  -- the expected total is at most `m * cHi`
  have hexp_le : C.expTotal ≤ (C.m : ℝ) * cHi := by
    have h1 : ∑ ω, C.P ω * C.totalSize ω ≤ ∑ ω, C.P ω * ((C.m : ℝ) * cHi) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (htot_le ω) (le_of_lt (C.hP ω))
    have h2 : ∑ ω, C.P ω * ((C.m : ℝ) * cHi) = (C.m : ℝ) * cHi := by
      rw [← Finset.sum_mul, C.hPsum, one_mul]
    rw [ChunkSystemB.expTotal]
    linarith [h1, h2 ▸ h1]
  -- every conditional expectation of the total is at least `m * cLo`
  have hce_ge : ∀ (n : ℕ) (ω : C.Ω), (C.m : ℝ) * cLo ≤ C.condExp C.totalSize n ω :=
    fun n ω => C.le_condExp fun ω' _ => hle_tot ω'
  have hce_le : ∀ (n : ℕ) (ω : C.Ω), C.condExp C.totalSize n ω ≤ (C.m : ℝ) * cHi :=
    fun n ω => C.condExp_le fun ω' _ => htot_le ω'
  refine ⟨?_, ?_, ?_⟩
  · -- L¹-sturdiness
    intro n _
    have hterm : ∀ ω : C.Ω,
        C.P ω * max (C.expTotal - C.condExp C.totalSize n ω) 0
          ≤ C.P ω * ((C.m : ℝ) * (cHi - cLo)) := by
      intro ω
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (C.hP ω))
      refine max_le ?_ hD0
      have h1 := hexp_le
      have h2 := hce_ge n ω
      nlinarith
    calc ∑ ω, C.P ω * max (C.expTotal - C.condExp C.totalSize n ω) 0
        ≤ ∑ ω, C.P ω * ((C.m : ℝ) * (cHi - cLo)) := Finset.sum_le_sum fun ω _ => hterm ω
      _ = (C.m : ℝ) * (cHi - cLo) := by rw [← Finset.sum_mul, C.hPsum, one_mul]
  · -- Doob jump bound
    intro h ω
    have h1 := hce_ge (h + 1) ω
    have h2 := hce_le (h + 1) ω
    have h3 := hce_ge h ω
    have h4 := hce_le h ω
    rw [abs_le]
    constructor
    · show -((C.m : ℝ) * (cHi - cLo)) ≤ C.doobTotal (h + 1) ω - C.doobTotal h ω
      unfold ChunkSystemB.doobTotal
      nlinarith
    · show C.doobTotal (h + 1) ω - C.doobTotal h ω ≤ (C.m : ℝ) * (cHi - cLo)
      unfold ChunkSystemB.doobTotal
      nlinarith
  · -- no chunk falls below the floor
    intro n hn
    have hzero : ∀ ω : C.Ω,
        (∑ i ∈ Finset.range n, if C.sizeN i ω < flo then (1 : ℝ) else 0) = 0 := by
      intro ω
      refine Finset.sum_eq_zero fun i hi => ?_
      have hin : i < n := Finset.mem_range.mp hi
      have him : i < C.m := lt_of_lt_of_le hin (le_trans hn hn₀)
      have : flo ≤ C.sizeN i ω := le_trans hflo (C.le_sizeN him ω)
      rw [if_neg (by linarith)]
    have : ∑ ω, C.P ω *
        (∑ i ∈ Finset.range n, if C.sizeN i ω < flo then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [hzero ω, mul_zero]
    linarith [this]
