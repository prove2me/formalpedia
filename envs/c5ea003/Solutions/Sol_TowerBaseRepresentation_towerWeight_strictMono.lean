-- Prove2me | solution 1 for TowerBaseRepresentation.towerWeight_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:31:05.853542+00:00
-- url     : https://prove2.me/submissions/ff8be6c7-02f9-4a57-bb82-2eb46590182e

-- Sol generated from NumberTheory/TowerBaseRepresentation.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix
import Definitions.Def_NumberTheory_TowerBaseRepresentation

/-!
# Tower-base representations

At position `k` the radix is `2^(towerWeight k)`.  Thus the alphabet itself grows
recursively.  This gives very few *digit positions*, but each high-position digit
comes from an enormous alphabet; the final theorem records the corresponding
bit-cost bound and prevents interpreting position count alone as compression.
-/

open TowerBaseRepresentation

open RecursiveMixedRadix














open TowerBaseRepresentation in
theorem solution: StrictMono towerWeight := by
  apply strictMono_nat_of_lt_succ
  intro k
  show towerWeight k < towerWeight (k + 1)
  simp [towerWeight]
  have hpos : 0 < towerWeight k := by
    induction k with
    | zero => simp [towerWeight]
    | succ m ih => simp [towerWeight, ih, pow_pos]
  have h2 : 1 < 2 ^ towerWeight k := by
    exact one_lt_pow₀ (by norm_num : 1 < 2) (by omega)
  calc towerWeight k = 1 * towerWeight k := by ring
    _ < 2 ^ towerWeight k * towerWeight k := Nat.mul_lt_mul_of_pos_right h2 hpos
