-- Prove2me | solution 1 for ReorderL7.signflip_window_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:51:58.368107+00:00
-- url     : https://prove2.me/submissions/15f3c40b-f0d7-4a81-b584-7b6efc322b6f

-- Sol generated from Novelty/ReorderWindowFamilyKeepFraction.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
import Definitions.Def_Novelty_ReorderWindowFamilyKeepFraction
import Theorems.Thm_ReorderL7_sqrt_one_add_pos
/-
# The sign flip is universal across window families, and the wheel law is a theorem

Fourth instalment of the GAP-L7' programme.  Two closures:

## A.  Window-ratio family : the sign flip is not an artefact of `q < 2p`

A generator that advertises `q < k·p` licenses the balance window
`[√N/√k, √N]`.  Repeating the round-76 analysis for a general window ratio gives
a closed-form crossover

`δ*(k) = 8√k(√k - 1)/(√k + 1)²`

(`signflip_window_family`), specialising to `80 - 56√2` at `k = 2`
(`crossoverWidthK_two`).  The decisive structural fact is

`crossoverWidthK_lt_band : 1 < k → δ*(k) < k - 1`,

i.e. **the crossover always lies strictly inside the admissible band range**.
So for *every* advertised balance ratio there are two admissible populations on
which the same two committed policies swap winners
(`signflip_universal`): the falsification of GAP-L7-as-drafted is not a corner
of the `q < 2p` convention, it is a property of the whole REORDER family.

## B.  L7-d : the structural keep fraction, extracted rather than booked

`card_coprime_block` counts the survivors of a mod-`M` wheel exactly:
`φ(M)·m` out of `M·m`.  Since a reordering is a bijection it cannot change that
count (`touched_card_reorder_invariant`), so `μ_eff = φ(M)/M` is a *conserved
quantity of the transcript*, not an experimenter's booking.  Feeding it into the
touch floor gives the protocol-A T1 law as a theorem:

`wheel_speedup_le : S ≤ M/φ(M)`,  and at `M = 30`,  `S ≤ 15/4 = 3.75`
(`wheel_thirty_law`) — the value the wheel arm measured as 3.7331–3.7496.

-- !-- Lab Notes -- !--
-- Monte-Carlo (n = 1500 per band, seed 20260831, genuine 24-bit semiprimes)
-- brackets the k = 2 crossover between delta = 0.80 (ascending still wins,
-- desc/asc = 1.0200) and delta = 0.75 (descending wins, desc/asc = 0.9273),
-- against the closed form 80 - 56*sqrt 2 = 0.804041 proved here.
-- Measured wheel speedups 3.7331 / 3.741 / 3.7496 sit under the derived
-- 15/4 = 3.75 ceiling, gaps 0.45% / 0.24% / 0.01%.
-/

open ReorderL7

open Finset

noncomputable section

/-! ## A.  The window-ratio family -/


lemma one_lt_sqrt_of_one_lt {k : ℝ} (hk : 1 < k) : 1 < Real.sqrt k := by
  have h1 : Real.sqrt 1 < Real.sqrt k := Real.sqrt_lt_sqrt (by norm_num) hk
  simpa using h1





/-! ## B.  The structural keep fraction of a wheel -/






/-! ## C.  General keyed residue control

The mod-3 control of `Novelty.ReorderMasterCapWitnesses` at an arbitrary modulus:
selecting one residue class promotes exactly the same number of candidates for
every key, so an `N`-keyed promotion rule is statistically indistinguishable
from a fixed-key one at *any* modulus. -/






open ReorderL7 in
theorem solution{k delta : ℝ} (hk : 1 < k) (h : 0 < delta) :
    (meanInvSqrt delta - 1 / Real.sqrt k < 1 - meanInvSqrt delta) ↔ crossoverWidthK k < delta := by
  set t := Real.sqrt k with htdef
  have ht1 : 1 < t := one_lt_sqrt_of_one_lt hk
  have htpos : 0 < t := by linarith
  set s := Real.sqrt (1 + delta) with hsdef
  have hs : s * s = 1 + delta := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 < s := sqrt_one_add_pos h
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hA : meanInvSqrt delta * (1 + s) = 2 := by
    rw [meanInvSqrt, ← hsdef]; field_simp
  have hB : (meanInvSqrt delta - 1 / t < 1 - meanInvSqrt delta) ↔ (4 * t < (t + 1) * (1 + s)) := by
    constructor
    · intro hlt
      have hmul : (2 * meanInvSqrt delta) * (t * (1 + s)) < (1 + 1 / t) * (t * (1 + s)) :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)
      have hinv : (1 / t) * t = 1 := by field_simp
      nlinarith [hmul, hA, hinv, htpos, h1s]
    · intro hlt
      by_contra hcon
      push_neg at hcon
      have hmul : (1 + 1 / t) * (t * (1 + s)) ≤ (2 * meanInvSqrt delta) * (t * (1 + s)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hinv : (1 / t) * t = 1 := by field_simp
      nlinarith [hmul, hA, hinv, htpos, h1s]
  have hC : (4 * t < (t + 1) * (1 + s)) ↔ crossoverWidthK k < delta := by
    have hden : (0:ℝ) < (t + 1) ^ 2 := by positivity
    rw [crossoverWidthK, ← htdef, div_lt_iff₀ hden]
    constructor
    · intro hlt
      have hstep : 3 * t - 1 < (t + 1) * s := by nlinarith [hlt]
      nlinarith [hstep, hs, ht1, htpos, hs1]
    · intro hlt
      have hnn : (0:ℝ) ≤ (t + 1) * s := mul_nonneg (by linarith) (by linarith)
      have hstep : 3 * t - 1 < (t + 1) * s := by
        by_contra hcon
        push_neg at hcon
        have hsq : ((t + 1) * s) * ((t + 1) * s) ≤ (3 * t - 1) * (3 * t - 1) :=
          mul_self_le_mul_self hnn hcon
        nlinarith [hsq, hs, ht1]
      nlinarith [hstep]
  rw [hB, hC]
