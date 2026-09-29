-- Prove2me | solution 1 for ReorderL7.card_residue_class_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:45:59.195984+00:00
-- url     : https://prove2.me/submissions/962a4b93-1a79-4bab-8569-65748b37bc93

-- Sol generated from Novelty/ReorderWindowFamilyKeepFraction.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
import Definitions.Def_Novelty_ReorderWindowFamilyKeepFraction
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
theorem solution(M m c : ℕ) (hM : 0 < M) (hc : c < M) :
    ({x ∈ Finset.range (M * m) | x % M = c}).card = m := by
  classical
  have h : ({x ∈ Finset.range (M * m) | x % M = c}).card = (Finset.range m).card := by
    refine Finset.card_bij' (fun x _ => x / M) (fun i _ => M * i + c) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact Nat.div_lt_of_lt_mul (by omega)
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]⟩
      calc M * i + c < M * i + M := by omega
        _ = M * (i + 1) := by ring
        _ ≤ M * m := Nat.mul_le_mul_left M hi
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      dsimp only
      rw [← hx.2, Nat.div_add_mod]
    · intro i hi
      dsimp only
      rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hc, Nat.add_zero]
  simpa using h
