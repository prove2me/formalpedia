-- Prove2me | solution 1 for DepthDecay.Adm.child
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:16:10.23952+00:00
-- url     : https://prove2.me/submissions/2d510876-23f7-4234-a74a-c110b1374fe5

-- Sol generated from Cryptography/DepthDecay/PathRealization.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_PathRealization
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# Realizing paths, and an entropy form of the depth decay

The first two files study the descent map `parent` and what a fixed-precision
magnitude probe can read off it.  Here we go the other way: we *build* states
from words, prove that the descent reads the word back letter by letter, and use
that to obtain a counting (pigeonhole) form of the depth decay which is
independent of the explicit straddling construction of
`Cryptography.DepthDecay.NullBeyondInversion`.

## Main results

* `Adm.child`, `letterOf_child`, `parent_child` : the three Berggren children are
  admissibility-preserving sections of the descent, and each child is tagged by
  its own letter.
* `letterAt_build` : the descent path of `build w` is the word `w`.  Every word
  is realized, so the tree really carries `3^k` distinct depth-`k` behaviours.
* `probe_mem_Ico` : on the stratum of states built from `{A,B}`-words the ratio
  stays in `(1,3)`, so a `W`-window probe takes at most `2·2^W` distinct values
  there.
* `probe_collision_of_depth` : **entropy form of the depth decay.**  Once
  `2·2^W < 2^k`, i.e. once the depth exceeds the window budget by two bits, the
  `W`-window sensor must confuse two admissible states whose paths differ at some
  depth below `k`.  The magnitude channel simply does not have the capacity to
  carry the deep letters.
-/

open DepthDecay









/-! ### The bounded-ratio stratum -/







/-! ### Entropy form of the depth decay -/



open DepthDecay in
theorem solution{s : ℕ × ℕ} (h : Adm s) (x : Letter) : Adm (DepthDecay.child x s) := by
  obtain ⟨hp, hlt, hg, hpar⟩ := h
  cases x with
  | A =>
    refine ⟨by simp [DepthDecay.child]; omega, by simp [DepthDecay.child]; omega, ?_,
      by simp [DepthDecay.child]; omega⟩
    have hdvd : Nat.gcd (2 * s.1 - s.2) s.1 ∣ Nat.gcd s.1 s.2 := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_right _ _) ?_
      have h1 : Nat.gcd (2 * s.1 - s.2) s.1 ∣ 2 * s.1 :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
      have h2 : Nat.gcd (2 * s.1 - s.2) s.1 ∣ 2 * s.1 - s.2 := Nat.gcd_dvd_left _ _
      have h3 := Nat.dvd_sub h1 h2
      rwa [show 2 * s.1 - (2 * s.1 - s.2) = s.2 by omega] at h3
    rw [hg] at hdvd
    simpa [DepthDecay.child] using Nat.eq_one_of_dvd_one hdvd
  | B =>
    refine ⟨by simp [DepthDecay.child]; omega, by simp [DepthDecay.child]; omega, ?_,
      by simp [DepthDecay.child]; omega⟩
    have hdvd : Nat.gcd (2 * s.1 + s.2) s.1 ∣ Nat.gcd s.1 s.2 := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_right _ _) ?_
      have h1 : Nat.gcd (2 * s.1 + s.2) s.1 ∣ 2 * s.1 :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
      have h2 : Nat.gcd (2 * s.1 + s.2) s.1 ∣ 2 * s.1 + s.2 := Nat.gcd_dvd_left _ _
      have h3 := Nat.dvd_sub h2 h1
      rwa [show 2 * s.1 + s.2 - 2 * s.1 = s.2 by omega] at h3
    rw [hg] at hdvd
    simpa [DepthDecay.child] using Nat.eq_one_of_dvd_one hdvd
  | C =>
    refine ⟨by simp [DepthDecay.child]; omega, by simp [DepthDecay.child]; omega, ?_,
      by simp [DepthDecay.child]; omega⟩
    have hdvd : Nat.gcd (s.1 + 2 * s.2) s.2 ∣ Nat.gcd s.1 s.2 := by
      refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      have h1 : Nat.gcd (s.1 + 2 * s.2) s.2 ∣ 2 * s.2 :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
      have h2 : Nat.gcd (s.1 + 2 * s.2) s.2 ∣ s.1 + 2 * s.2 := Nat.gcd_dvd_left _ _
      have h3 := Nat.dvd_sub h2 h1
      rwa [show s.1 + 2 * s.2 - 2 * s.2 = s.1 by omega] at h3
    rw [hg] at hdvd
    simpa [DepthDecay.child] using Nat.eq_one_of_dvd_one hdvd
