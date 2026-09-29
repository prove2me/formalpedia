-- Prove2me | solution 1 for ProofSpace.exists_first_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:52:13.150966+00:00
-- url     : https://prove2.me/submissions/4978f252-4dae-4001-b6f6-86027ada949b

-- Sol generated from Logic/ProofSpaceTransition.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransition

/-!
# A discrete Gödel threshold in finite proof space

This file gives a precise finite model of the proposed phase-transition picture.
At cutoff `n`, `provable n` and `unprovable n` count the two classes of statements
seen so far.  Their difference is the signed order parameter.  The main theorem
shows that, whenever this difference starts positive and ends nonpositive, there
is a unique first cutoff at which the provable majority disappears.  Under a
strict-decrease hypothesis, the sign change is permanent and its location is
unique.

This is deliberately a theorem about an abstract enumeration: incompleteness
alone does not imply any particular asymptotic density or power law without a
choice of syntax, length function, and probability measure.
-/

open ProofSpace













open ProofSpace in
theorem solution(f : ℕ → ℤ) (N : ℕ)
    (hN : f N ≤ 0) :
    ∃ n ≤ N, IsFirstThreshold f n := by
  -- The set of n ≤ N with f n ≤ 0 is nonempty (contains N)
  let S : Finset ℕ := {n ∈ Finset.range (N + 1) | f n ≤ 0}
  have hne : S.Nonempty := by
    use N
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self N), hN⟩
  -- Take the minimum
  let n := S.min' hne
  have hn_mem : n ∈ S := Finset.min'_mem S hne
  have hn_bound : n ≤ N := Finset.mem_range_succ_iff.mp (Finset.mem_filter.mp hn_mem).1
  use n, hn_bound
  refine ⟨(Finset.mem_filter.mp hn_mem).2, ?_⟩
  intro m hm
  by_contra h
  have h_nonpos : f m ≤ 0 := le_of_not_gt h
  have hm_in_S : m ∈ S := by
    have hm' : m < N + 1 := Nat.lt_succ_of_lt (hm.trans_le hn_bound)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm', h_nonpos⟩
  have := S.min'_le _ hm_in_S
  omega
