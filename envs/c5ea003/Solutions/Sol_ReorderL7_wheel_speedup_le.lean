-- Prove2me | solution 1 for ReorderL7.wheel_speedup_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:01.476838+00:00
-- url     : https://prove2.me/submissions/ad707931-07b2-4ae0-9ae2-ed1a7bbb2c7b

-- Sol generated from Novelty/ReorderWindowFamilyKeepFraction.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
import Definitions.Def_Novelty_ReorderWindowFamilyKeepFraction
import Theorems.Thm_ReorderL7_speedup_le_inv_mu
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







/-! ## B.  The structural keep fraction of a wheel -/






/-! ## C.  General keyed residue control

The mod-3 control of `Novelty.ReorderMasterCapWitnesses` at an arbitrary modulus:
selecting one residue class promotes exactly the same number of candidates for
every key, so an `N`-keyed promotion rule is statistically indistinguishable
from a fixed-key one at *any* modulus. -/






open ReorderL7 in
theorem solution{M m : ℕ} (hM : 0 < M) (hphi : 0 < Nat.totient M) :
    ((((M * m : ℕ) : ℝ) + 1) / 2) / (((((Nat.totient M * m : ℕ) : ℝ)) + 1) / 2)
      ≤ (M : ℝ) / (Nat.totient M : ℝ) := by
  have hMR : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hphiR : (0:ℝ) < (Nat.totient M : ℝ) := by exact_mod_cast hphi
  have hle : (Nat.totient M : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
  have hmu : (0:ℝ) < (Nat.totient M : ℝ) / (M : ℝ) := by positivity
  have hmu1 : (Nat.totient M : ℝ) / (M : ℝ) ≤ 1 := by
    rw [div_le_one hMR]; exact hle
  have hkeq : ((Nat.totient M : ℝ) / (M : ℝ)) * ((M : ℝ) * (m : ℝ))
      = (Nat.totient M : ℝ) * (m : ℝ) := by field_simp
  have hk : ((Nat.totient M : ℝ) / (M : ℝ)) * ((M * m : ℕ) : ℝ)
      ≤ ((Nat.totient M * m : ℕ) : ℝ) := by
    push_cast
    rw [hkeq]
  have h := speedup_le_inv_mu (M := M * m) (k := Nat.totient M * m) hmu hmu1 hk
  have hinv : 1 / ((Nat.totient M : ℝ) / (M : ℝ)) = (M : ℝ) / (Nat.totient M : ℝ) := by
    field_simp
  rw [hinv] at h
  exact h
