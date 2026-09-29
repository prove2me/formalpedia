-- Prove2me | solution 1 for NeuralCodePlotkinTightness.affineWord_dist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:50:29.632167+00:00
-- url     : https://prove2.me/submissions/2285d121-897a-43d0-9733-eecb9b652de0

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodePlotkinTightness_card_ip_eq

/-!
# Neural Coding: tightness of the Plotkin bound (Hadamard populations)

`Catalog/Novelty/NeuralCodeCapacityBounds.lean` proves the Plotkin bound: a
`d`-separated codebook on `N` neurons with `N < 2d` satisfies
`|C| * (2d - N) ≤ 2d`.  At the boundary `N = 2d` that inequality degenerates,
and the correct statement `A(2d, d) ≤ 4d` needs a *shortening* argument.  This
file proves that bound and shows it is **attained** whenever `2d` is a power of
two, by the affine (first-order Reed–Muller / Hadamard) neural code.

## Main results

* `maxCodeSize_shorten` — shortening on one neuron: `A(N+1, d) ≤ 2 * A(N, d)`.
* `plotkin_boundary` — the boundary Plotkin bound `A(2d, d) ≤ 4d`.
* `affineCode_separated`, `card_affineCode` — the affine code on `2 ^ (m+1)`
  neurons has `2 ^ (m+2)` codewords, pairwise at Hamming distance at least
  `2 ^ m`.
* `hadamard_capacity` — **Plotkin is tight**: `A(2 ^ (m+1), 2 ^ m) = 2 ^ (m+2)`.
  A population of `N = 2 ^ (m+1)` neurons that must tolerate `2 ^ m - 1`
  misfirings represents exactly `2N` concepts, realised by the affine code.
* `hadamard_capacity_half` — the same statement written as
  `A(N, N/2) = 2N` for `N` a power of two.
* `hadamard_capacity_rate` — the corresponding rate statement.

The smallest instances agree with the exhaustive search recorded in
`ComputationalEvidence.md`: `A(2,1) = 4` and `A(4,2) = 8`.
-/

open NeuralCodePlotkinTightness

open Finset NeuralCodeCapacity

/-! ## Shortening: `A(N+1, d) ≤ 2 * A(N, d)` -/




/-! ## The affine (Hadamard) neural code

Neurons are indexed by the `2 ^ k` binary strings of length `k`; a concept is a
pair `(a, b)` with `a` a string of length `k` and `b` a bit, and the pattern it
evokes fires neuron `x` exactly when the affine form `⟨a, x⟩ + b` is odd. -/


lemma bit_xor (b b' : Bool) : bit (xor b b') = bit b + bit b' := by
  cases b <;> cases b' <;> decide



/-- The zero string is orthogonal to everything. -/
lemma ip_zero {k : ℕ} (x : Fin k → Bool) : ip (fun _ => false) x = 0 := by
  simp [ip, bit]

/-- Additivity of the inner product in its first argument. -/
lemma ip_add {k : ℕ} (a a' x : Fin k → Bool) :
    ip a x + ip a' x = ip (fun i => xor (a i) (a' i)) x := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bit_xor]
  ring




/-- Two affine codewords disagree at `x` exactly on a level set of the
difference of their linear parts. -/
lemma affineWord_ne_iff {k : ℕ} (a a' x : Fin k → Bool) (b b' : Bool) :
    (affineWord a b x ≠ affineWord a' b' x)
      ↔ ip (fun i => xor (a i) (a' i)) x = bit b + bit b' + 1 := by
  unfold affineWord
  rw [← ip_add]
  generalize ip a x = z
  generalize ip a' x = w
  cases b <;> cases b' <;> revert z w <;> decide







/-! ## Tightness -/





open NeuralCodePlotkinTightness in
theorem solution{k : ℕ} (a a' : Fin k → Bool) (b b' : Bool)
    (h : (a, b) ≠ (a', b')) :
    2 ^ k / 2 ≤ hammingDist (affineWord a b) (affineWord a' b') := by
  classical
  by_cases haa : a = a'
  · -- same linear part, different constant: the patterns are complementary
    subst haa
    have hbb : b ≠ b' := fun hb => h (by rw [hb])
    have hzero : (fun i => xor (a i) (a i)) = fun _ => false := by
      funext i; cases a i <;> rfl
    have hall : ∀ x : Fin k → Bool, affineWord a b x ≠ affineWord a b' x := by
      intro x
      rw [affineWord_ne_iff, hzero, ip_zero]
      cases b <;> cases b' <;> first | exact absurd rfl hbb | decide
    have hdist : hammingDist (affineWord a b) (affineWord a b') = 2 ^ k := by
      rw [hammingDist, Finset.filter_true_of_mem (fun x _ => hall x)]
      simp
    rw [hdist]
    exact Nat.div_le_self _ _
  · -- different linear parts: exactly half the neurons differ
    have hu : ∃ j, (fun i => xor (a i) (a' i)) j = true := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp haa
      exact ⟨j, by cases hh : a j <;> cases hh' : a' j <;> simp_all⟩
    have hset : (Finset.univ.filter fun x => affineWord a b x ≠ affineWord a' b' x)
        = (Finset.univ.filter fun x => ip (fun i => xor (a i) (a' i)) x
            = bit b + bit b' + 1) :=
      Finset.filter_congr fun x _ => affineWord_ne_iff a a' x b b'
    rw [hammingDist, hset, card_ip_eq hu _]
