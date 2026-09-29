-- Prove2me | solution 1 for ECAFixedVariety.rule150_eq_zero_of_two_zeros
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:13:25.626333+00:00
-- url     : https://prove2.me/submissions/8943925f-b6b3-497a-8135-ca0a3f09a703

-- Sol generated from Novelty/ECAParityRule150.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Definitions.Def_Novelty_ECAParityRule150
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff

/-!
# Cycle 5: parity rigidity of Rule 150

Rule 150, `f(l,c,r) = l + c + r`, is the second classical additive automaton and
is placed in Wolfram class 3 (chaotic).  Its fixed-point equations read
`l + r = 0`, i.e. `s_{i-1} = s_{i+1}`: the variety is the space of
**period-two** configurations.  Consequently its dimension is controlled by the
parity of the ring size, and never exceeds `2`:

* `rule150_period_two` — every stationary configuration has spatial period `2`.
* `rule150_fixedSet_of_odd` — for odd `n` the variety is exactly the pair of
  constant configurations `{0, 1}`; so if a dimension exists it equals `1`.
* `rule150_alternating_mem` — for even `n` the alternating configuration
  (the reduction map `ZMod n → ZMod 2`) is a non-constant stationary point, so
  the variety strictly grows.
* `rule150_hasFixedDim_le_two` and `rule150_dim_lt_half` — the dimension is at
  most `2` for every `n`, so this class-3 rule violates the conjectured
  `dim ≥ n/2` for all `n ≥ 5`.

Together with the mod-3 dichotomy of Rules 90 and 45 this exhibits the general
phenomenon: the fixed-point variety of an additive rule is the kernel of a
circulant matrix, and its dimension is a *number-theoretic* function of `n` —
never a Wolfram class.
-/

open ECAFixedVariety

/-- Rule 150 is the additive rule `l + c + r`; stationarity says `l + r = 0`. -/
lemma rule150_local_iff : ∀ l c r : ZMod 2, localRuleZ 150 l c r = c ↔ l + r = 0 := by decide


/-- **Transfer relation for Rule 150.**  Stationary configurations have spatial
period two. -/
theorem rule150_period_two {n : ℕ} {s : Cfg n} (hs : s ∈ fixedSet 150 n) :
    ∀ i, s (i + 2) = s i := by
  rw [mem_fixedSet_iff] at hs
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  intro i
  have h1 := hs (i + 1)
  rw [show i + 1 - 1 = i from by ring, show i + 1 + 1 = i + 2 from by ring,
    rule150_local_iff] at h1
  exact key _ _ h1











open ECAFixedVariety in
theorem solution{n : ℕ} [NeZero n] {s : Cfg n}
    (hs : s ∈ fixedSet 150 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by
  have hper := rule150_period_two hs
  have key : ∀ k : ℕ, s ((k : ℕ) : ZMod n) = 0 ∧ s (((k + 1 : ℕ) : ℕ) : ZMod n) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1⟩
    | succ m ih =>
        obtain ⟨hm, hm1⟩ := ih
        refine ⟨by simpa using hm1, ?_⟩
        have e : ((m + 1 + 1 : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) + 2 := by push_cast; ring
        rw [e, hper, hm]
  funext i
  show s i = 0
  have hi : ((i.val : ℕ) : ZMod n) = i := by simp [ZMod.natCast_val, ZMod.cast_id]
  have hk := (key i.val).1
  rwa [hi] at hk
