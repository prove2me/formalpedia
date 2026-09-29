-- Prove2me | solution 1 for ECAFixedVariety.rule150_fixedSet_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:36.182199+00:00
-- url     : https://prove2.me/submissions/7d5cc04e-5ec1-4b29-91b0-a6b7b241fb24

-- Sol generated from Novelty/ECAParityRule150.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Definitions.Def_Novelty_ECAParityRule150
import Theorems.Thm_ECAFixedVariety_constant_of_shift_one
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff
import Theorems.Thm_ECAFixedVariety_shift_one_of_period_coprime
import Theorems.Thm_ECAFixedVariety_zmod2_eq_zero_or_one

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

/-- Constant configurations are stationary for Rule 150. -/
lemma rule150_const_mem {n : ℕ} (a : ZMod 2) :
    (fun _ : ZMod n => a) ∈ fixedSet 150 n := by
  rw [mem_fixedSet_iff]
  intro i
  have : ∀ x : ZMod 2, localRuleZ 150 x x x = x := by decide
  exact this a










open ECAFixedVariety in
theorem solution{n : ℕ} (hn : ¬ (2 ∣ n)) :
    fixedSet 150 n = {0, 1} := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, rfl⟩
  haveI : NeZero n := ⟨hn0⟩
  have hcop : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hn
  ext s
  constructor
  · intro hs
    have hper : ∀ i, s (i + ((2 : ℕ) : ZMod n)) = s i := by
      intro i
      have := rule150_period_two hs i
      simpa using this
    have hconst := constant_of_shift_one (shift_one_of_period_coprime hn0 hcop hper)
    rcases zmod2_eq_zero_or_one (s 0) with h0 | h0
    · left
      funext i
      simpa [h0] using hconst i
    · right
      funext i
      simpa [h0] using hconst i
  · rintro (rfl | rfl)
    · exact rule150_const_mem 0
    · exact rule150_const_mem 1
