-- Prove2me | solution 1 for ProofSpace.sharp_transition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:27.822351+00:00
-- url     : https://prove2.me/submissions/f15a78b6-d0ee-4b1e-881d-35d3494347a7

-- Sol generated from Logic/ProofSpaceTransition.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransition
import Theorems.Thm_ProofSpace_exists_first_threshold

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





/-- The first threshold is unique, without any monotonicity assumption. -/
theorem first_threshold_unique (f : ℕ → ℤ) {a b : ℕ}
    (ha : IsFirstThreshold f a) (hb : IsFirstThreshold f b) : a = b := by
  apply Nat.le_antisymm
  · by_contra h
    push_neg at h
    have : 0 < f b := ha.2 b h
    linarith [hb.1]
  · by_contra h
    push_neg at h
    have : 0 < f a := hb.2 a h
    linarith [ha.1]








open ProofSpace in
theorem solution(f : ℕ → ℤ) (N : ℕ)
    (hdec : ∀ n < N, f (n + 1) < f n)
    (hN : f N ≤ 0) :
    ∃! n, n ≤ N ∧ IsFirstThreshold f n ∧
      ∀ m, n < m → m ≤ N → f m < 0 := by
  have hstrict : ∀ n m, n < m → m ≤ N → f m < f n := by
    intro n m hnm hmN
    induction m generalizing n with
    | zero => omega
    | succ m ih =>
      rcases lt_trichotomy n m with hnm' | rfl | hmn
      · have ih' := ih n hnm' (Nat.le_of_succ_le hmN)
        linarith [hdec m (Nat.lt_of_succ_le hmN)]
      · exact hdec n (Nat.lt_of_succ_le hmN)
      · omega
  obtain ⟨n, hn_le, hn_ft⟩ := exists_first_threshold f N hN
  use n
  refine ⟨⟨hn_le, hn_ft, ?_⟩, ?_⟩
  · intro m hnm hmN
    have := hstrict n m hnm hmN
    linarith [hn_ft.1]
  · intro y ⟨_, hy_ft, _⟩
    exact first_threshold_unique f hy_ft hn_ft
