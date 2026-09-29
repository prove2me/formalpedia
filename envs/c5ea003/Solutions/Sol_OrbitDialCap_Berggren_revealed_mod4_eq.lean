-- Prove2me | solution 1 for OrbitDialCap.Berggren.revealed_mod4_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:33.08723+00:00
-- url     : https://prove2.me/submissions/7ed300cc-f4ba-4c10-9902-b080ab83bd56

-- Sol generated from Tropical/OrbitDialInvariants.lean
import Mathlib
import Definitions.Def_Tropical_OrbitDialInvariants

/-!
# Berggren-tree orbit invariants: the revealed residue set is universal

This file formalises the *characterisation arm* of the ORBIT-DIAL-CAP-TEST
(FACT round-74 #2, exp 564): the residues revealed by the root component of the
Berggren triplet tree are fixed once and for all, so the "orbit dial" they define is
the same table for every semiprime `N`.

## Contents

* `OrbitDialCap.Berggren.InTree` — the root component of the Berggren tree, generated
  from `(3,4,5)` by the three unimodular matrices `B₁, B₂, B₃`.
* `OrbitDialCap.Berggren.inTree_isPT` — every node is a Pythagorean triple.
* `OrbitDialCap.Berggren.inTree_congruence` — the congruence invariant of the whole
  component: `a` odd, `4 ∣ b`, `c ≡ 1 (mod 4)`.
* `OrbitDialCap.Berggren.revealed_mod4_eq` — **the revealed residue set mod 4 is the
  fixed two-element set `{(1,0,1), (3,0,1)}`**, hence carries no parameter dependence:
  the orbit dial is one universal exclusion table.
* `OrbitDialCap.Berggren.three_dvd_leg_mul` — barrier 6 restated as a primitive-triple
  congruence: `3` divides a leg of every Pythagorean triple.
* `OrbitDialCap.Berggren.parity_dial_sound` — the bridge to factoring: the parity skip
  never discards a divisor of an odd `N`, i.e. it has soundness `s = 1`.
-/

open OrbitDialCap
open Berggren







/-- **The congruence invariant of the root component.**  Every node has odd first leg,
second leg divisible by `4`, and hypotenuse `≡ 1 (mod 4)`.  The three Berggren moves
preserve this class, so no BFS budget — and in particular no choice of a target `N` —
can enlarge the revealed set. -/
theorem inTree_congruence {t : ℤ × ℤ × ℤ} (h : InTree t) :
    t.1 % 2 = 1 ∧ t.2.1 % 4 = 0 ∧ t.2.2 % 4 = 1 := by
  induction h with
  | root => norm_num
  | step1 _ ih => simp only [B1]; omega
  | step2 _ ih => simp only [B2]; omega
  | step3 _ ih => simp only [B3]; omega

/-- The node `(5,12,13)`, the first `B₁`-child of the root. -/
theorem inTree_five_twelve_thirteen : InTree (5, 12, 13) := by
  have h := InTree.step1 InTree.root
  norm_num [B1] at h
  exact h


private lemma cast_of_emod {t : ℤ} {r : ℕ} (h : t % 4 = (r : ℤ)) :
    (t : ZMod 4) = (r : ZMod 4) := by
  have hdvd : (4 : ℤ) ∣ t - (r : ℤ) := by omega
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (t - (r : ℤ)) 4).mpr hdvd
  push_cast at this
  linear_combination this











open OrbitDialCap.Berggren in
theorem solution:
    revealedMod4 =
      {((1 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4)), ((3 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4))} := by
  ext r
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h1, h2, h3⟩ := inTree_congruence ht
    have e2 : (t.2.1 : ZMod 4) = 0 := by
      have := cast_of_emod (t := t.2.1) (r := 0) (by exact_mod_cast h2)
      simpa using this
    have e3 : (t.2.2 : ZMod 4) = 1 := by
      have := cast_of_emod (t := t.2.2) (r := 1) (by exact_mod_cast h3)
      simpa using this
    rcases (by omega : t.1 % 4 = 1 ∨ t.1 % 4 = 3) with h | h
    · left
      have e1 := cast_of_emod (t := t.1) (r := 1) (by exact_mod_cast h)
      simp [e1, e2, e3]
    · right
      have e1 := cast_of_emod (t := t.1) (r := 3) (by exact_mod_cast h)
      simp [e1, e2, e3]
  · rintro (rfl | rfl)
    · exact ⟨(5, 12, 13), inTree_five_twelve_thirteen, by decide⟩
    · exact ⟨(3, 4, 5), InTree.root, by decide⟩
