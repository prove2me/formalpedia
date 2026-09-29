-- Prove2me | solution 1 for AlmostLossless.exists_scanScheme_of_code
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:23:11.930635+00:00
-- url     : https://prove2.me/submissions/2cec17ba-3914-4750-89d4-140d9eaab068

-- Sol generated from Logic/AlmostLossless/Optimality.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
import Theorems.Thm_AlmostLossless_correct_scanCode
import Theorems.Thm_AlmostLossless_honest_scanCode

/-!
# Optimality: randomness is never useful, and honesty is free

Two structural results that close the loop opened by `Core` and `Scheme`.

* `AlmostLossless.randomized_epsilon_pigeonhole` — the exact `ε`-pigeonhole
  characterisation survives randomisation: if *any* randomized ensemble of codes
  has average failure probability `≤ ε`, then already a set of `≤ |C|` source
  words carries probability `≥ 1 - ε`, so a *deterministic* code achieves the
  same `ε`.  Shared randomness buys nothing, for **every** source (the earlier
  `randomized_avg_failProb_lower` was the uniform-source special case).

* `AlmostLossless.exists_scanScheme_of_code` — conversely, *every* code, honest
  or not, is matched on its correct set by a uniqueness-scan code, whose decoder
  probes at most **one** candidate.  So the "no silent corruption" guarantee
  costs one extra alphabet symbol and nothing else: no checksum, no rate loss
  beyond `+1`, no decoding time.
-/

open AlmostLossless

open Finset

variable {S C : Type*} [Fintype S] [DecidableEq S]

/-! ## Randomness never helps -/




/-! ## Honesty is free -/

omit [Fintype S] [DecidableEq S] in
/-- The encoder is injective on the correctly decoded words. -/
theorem injOn_enc_of_correct (K : Code S C) {x y : S} (hx : Correct K x) (hy : Correct K y)
    (h : K.enc x = K.enc y) : x = y := by
  have : (some x : Option S) = some y := by
    unfold Correct at hx hy
    rw [← hx, ← hy, h]
  exact Option.some_inj.mp this



open AlmostLossless in
theorem solution[DecidableEq C] (K : Code S C) :
    ∃ P : ScanScheme S Unit C,
      (∀ s : S, Correct (P.code ()) s ↔ Correct K s) ∧
      Honest (P.code ()) ∧
      (∀ m : C, P.decodeCost () m ≤ 1) := by
  classical
  refine ⟨{ typical := ({s | Correct K s} : Finset S)
            hash := fun _ s => K.enc s
            cand := fun _ m => {s ∈ ({s | Correct K s} : Finset S) | K.enc s = m}
            cand_subset := fun _ _ => Finset.filter_subset _ _
            self_mem_cand := fun _ _ hs => Finset.mem_filter.2 ⟨hs, rfl⟩ }, ?_, ?_, ?_⟩
  · intro s
    constructor
    · intro hcor
      by_contra hK
      have hK' : ¬ (K.dec (K.enc s) = some s) := hK
      simp [Correct, ScanScheme.code, hK'] at hcor
    · intro hK
      have hs : s ∈ ({s | Correct K s} : Finset S) := by simpa using hK
      refine correct_scanCode _ () ?_ hs
      intro x hx y hy hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact injOn_enc_of_correct K hx hy hxy
  · exact honest_scanCode _ ()
  · intro m
    show ({s ∈ ({s | Correct K s} : Finset S) | K.enc s = m} : Finset S).card ≤ 1
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact injOn_enc_of_correct K hx.1 hy.1 (by rw [hx.2, hy.2])
