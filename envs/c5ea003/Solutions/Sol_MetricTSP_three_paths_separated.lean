-- Prove2me | solution 1 for MetricTSP.three_paths_separated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:45:28.896736+00:00
-- url     : https://prove2.me/submissions/85cc56cd-0aa7-46cb-a976-88d6e0f01cf2

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

variable {k : ℕ}

lemma nat_dist_def4 (a b : ℕ) : Nat.dist a b = (a - b) + (b - a) := rfl

lemma tpSpec4 (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := by
  have hv := v.isLt
  unfold tpPath tpPos
  by_cases h : v.val = 0 ∨ v.val = 3*k+1
  · rw [if_pos h]
    left
    rcases h with h | h <;> rw [h] <;> simp <;> omega
  · rw [if_neg h]
    right
    push_neg at h
    have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    rw [if_neg h.1, if_neg h.2]
    omega

lemma tpCoord_inj4 (hk : 1 ≤ k) (u v : Fin (3*k+2))
    (hp : tpPath k u = tpPath k v) (hq : tpPos k u = tpPos k v) : u = v := by
  have hu := u.isLt
  have hv := v.isLt
  apply Fin.ext
  unfold tpPath at hp
  unfold tpPos at hq
  by_cases h1 : u.val = 0 ∨ u.val = 3*k+1 <;> by_cases h2 : v.val = 0 ∨ v.val = 3*k+1
  · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      rw [h1, h2] at hq
      rw [if_pos rfl] at hq
      rw [if_neg (by omega), if_pos rfl] at hq
      omega
    · exfalso
      rw [h1, h2] at hq
      rw [if_neg (by omega), if_pos rfl, if_pos rfl] at hq
      omega
    · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at hp
    push_neg at h2
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · rw [if_neg h1, if_pos h2] at hp
    push_neg at h1
    have hdivlt : (u.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · push_neg at h1 h2
    rw [if_neg h1.1, if_neg h1.2] at hq
    rw [if_neg h2.1, if_neg h2.2] at hq
    rw [if_neg (not_or.mpr h1), if_neg (not_or.mpr h2)] at hp
    have e1 : k * ((u.val - 1) / k) + (u.val - 1) % k = u.val - 1 := Nat.div_add_mod _ k
    have e2 : k * ((v.val - 1) / k) + (v.val - 1) % k = v.val - 1 := Nat.div_add_mod _ k
    rw [hp] at e1
    have e3 : (u.val - 1) % k = (v.val - 1) % k := by omega
    rw [e3] at e1
    omega

theorem three_paths_separated_thm (k : ℕ) (hk : 1 ≤ k) :
    ∀ u v : Fin (3*k+2), u ≠ v → (1 : ℝ) ≤ tpCost k u v := by
  intro u v huv
  unfold tpCost
  have hd1 : 1 ≤ tpDist k u v := by
    by_contra h0
    have hz : tpDist k u v = 0 := by omega
    apply huv
    have hu := tpSpec4 hk u
    have hv := tpSpec4 hk v
    unfold tpDist at hz
    by_cases hsh : tpPath k u = 3 ∨ tpPath k v = 3 ∨ tpPath k u = tpPath k v
    · rw [if_pos hsh] at hz
      rw [nat_dist_def4] at hz
      have hpos : tpPos k u = tpPos k v := by omega
      have hpath : tpPath k u = tpPath k v := by omega
      exact tpCoord_inj4 hk u v hpath hpos
    · rw [if_neg hsh] at hz
      push_neg at hsh
      exfalso
      omega
  exact_mod_cast hd1

end MetricTSP

open MetricTSP

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∀ u v : Fin (3*k+2), u ≠ v → (1 : ℝ) ≤ tpCost k u v :=
  MetricTSP.three_paths_separated_thm k hk
