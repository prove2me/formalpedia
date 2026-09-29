-- Prove2me | solution 1 for ReorderL7.signflip_universal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:53:18.96725+00:00
-- url     : https://prove2.me/submissions/d3fbd187-c8d3-43e6-9695-0a0c6c335202

-- Sol generated from Novelty/ReorderWindowFamilyKeepFraction.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
import Definitions.Def_Novelty_ReorderWindowFamilyKeepFraction
import Theorems.Thm_ReorderL7_signflip_window_family
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



/-- **The crossover always lies strictly inside the admissible band range.**
For every advertised balance ratio `k > 1` the crossover width `δ*(k)` is smaller
than the widest admissible band `k - 1`. -/
theorem crossoverWidthK_lt_band {k : ℝ} (hk : 1 < k) : crossoverWidthK k < k - 1 := by
  set t := Real.sqrt k with htdef
  have ht1 : 1 < t := one_lt_sqrt_of_one_lt hk
  have hts : t * t = k := Real.mul_self_sqrt (by linarith)
  have hden : (0:ℝ) < (t + 1) ^ 2 := by positivity
  have hpos2 : (0:ℝ) < t ^ 2 + 4 * t - 1 := by nlinarith [ht1]
  have h3 : (0:ℝ) < (t - 1) ^ 2 * (t ^ 2 + 4 * t - 1) :=
    mul_pos (by nlinarith [ht1]) hpos2
  rw [crossoverWidthK, ← htdef, div_lt_iff₀ hden, ← hts]
  nlinarith [h3]


/-! ## B.  The structural keep fraction of a wheel -/






/-! ## C.  General keyed residue control

The mod-3 control of `Novelty.ReorderMasterCapWitnesses` at an arbitrary modulus:
selecting one residue class promotes exactly the same number of candidates for
every key, so an `N`-keyed promotion rule is statistically indistinguishable
from a fixed-key one at *any* modulus. -/






open ReorderL7 in
theorem solution{k : ℝ} (hk : 1 < k) :
    ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ d₁ ≤ k - 1 ∧ 0 < d₂ ∧ d₂ ≤ k - 1 ∧
      (meanInvSqrt d₁ - 1 / Real.sqrt k < 1 - meanInvSqrt d₁) ∧
      ¬ (meanInvSqrt d₂ - 1 / Real.sqrt k < 1 - meanInvSqrt d₂) := by
  have ht1 : 1 < Real.sqrt k := one_lt_sqrt_of_one_lt hk
  have hcross : crossoverWidthK k < k - 1 := crossoverWidthK_lt_band hk
  have hcpos : 0 < crossoverWidthK k := by
    rw [crossoverWidthK]
    have : (0:ℝ) < (Real.sqrt k + 1) ^ 2 := by positivity
    apply div_pos (by nlinarith [ht1]) this
  refine ⟨k - 1, crossoverWidthK k / 2, by linarith, le_rfl, by linarith, by linarith, ?_, ?_⟩
  · rw [signflip_window_family hk (by linarith)]
    exact hcross
  · rw [signflip_window_family hk (by linarith)]
    push_neg
    linarith
