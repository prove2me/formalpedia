-- Prove2me | solution 1 for Cryptography.BerggrenModular.card_nullCone_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:25:32.491479+00:00
-- url     : https://prove2.me/submissions/a42c5be9-73bd-4d16-bb50-aee8effb6e50

-- Sol generated from Cryptography/BerggrenModular/NullCone.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Definitions.Def_Cryptography_BerggrenModular_NullCone

/-!
# The reachable set lives on the punctured null cone, and the sharpened bound

Every Berggren move lies in `GL₃(ℤ)` and preserves the Lorentz form.  Hence the
whole Berggren tree consists of **primitive** null vectors, and its reduction
modulo a prime `p` lands in

```
Cone p = { w ∈ (ℤ/p)³ : w₁² + w₂² = w₃² } \ {0}.
```

Because a quadratic equation has at most two roots in a field, `|Cone p| ≤ 2p²`.
So the adversary's observation lives in a set of size `O(p²)`, not `p³`, and the
information-theoretic bounds of `Cryptography.BerggrenModular.Hardness` improve
by a whole factor of `p`.

## Main results

* `Prim_applyWord` — every state of the Berggren tree is a primitive triple.
* `stateMod_ne_zero` — modulo a prime the observed state is never `0`.
* `lorentzM_stateMod` — the observation always satisfies `a² + b² = c²` mod `m`.
* `card_nullCone_le` — the null cone modulo a prime has at most `2p²` points.
* `mod_ambiguity_lower_bound_of_subset` — the pigeonhole bound relative to any
  finite superset of the reachable states.
* `prime_ambiguity_lower_bound`, `not_modSeedRecoverable_of_card_prime` —
  the sharpened `Ω(3^k / 2p²)` ambiguity and the improved impossibility
  threshold `2p² < 3^k`.
-/

open Cryptography
open BerggrenModular

/-! ## Primitivity -/





/-! ## The observation lies on the punctured null cone -/




/-! ## Counting the null cone modulo a prime -/




/-! ## Sharpened ambiguity -/





open Cryptography.BerggrenModular in
theorem solution(p : ℕ) [Fact (Nat.Prime p)] :
    (nullCone p).card ≤ 2 * p ^ 2 := by
  classical
  have hmaps : ∀ w ∈ nullCone p, (w.1, w.2.1) ∈ (Finset.univ : Finset (ZMod p × ZMod p)) :=
    fun w _ => Finset.mem_univ _
  have hfib : ∀ q ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      ((nullCone p).filter (fun w => (w.1, w.2.1) = q)).card ≤ 2 := by
    intro q _
    rcases Finset.eq_empty_or_nonempty ((nullCone p).filter (fun w => (w.1, w.2.1) = q)) with
      he | ⟨w₀, hw₀⟩
    · simp [he]
    · have hsub : (nullCone p).filter (fun w => (w.1, w.2.1) = q) ⊆
          ({(q.1, q.2, w₀.2.2), (q.1, q.2, -w₀.2.2)} : Finset (TriM p)) := by
        intro w hw
        simp only [Finset.mem_filter, nullCone, Finset.mem_univ, true_and] at hw hw₀
        obtain ⟨hwc, hwq⟩ := hw
        obtain ⟨hw0c, hw0q⟩ := hw₀
        have hq1 : w.1 = q.1 := congrArg Prod.fst hwq
        have hq2 : w.2.1 = q.2 := congrArg Prod.snd hwq
        have hq1' : w₀.1 = q.1 := congrArg Prod.fst hw0q
        have hq2' : w₀.2.1 = q.2 := congrArg Prod.snd hw0q
        have hsq : w.2.2 ^ 2 = w₀.2.2 ^ 2 := by
          have e1 : w.1 ^ 2 + w.2.1 ^ 2 = w.2.2 ^ 2 := by
            have := hwc; simp only [lorentzM] at this; linear_combination this
          have e2 : w₀.1 ^ 2 + w₀.2.1 ^ 2 = w₀.2.2 ^ 2 := by
            have := hw0c; simp only [lorentzM] at this; linear_combination this
          rw [← e1, ← e2, hq1, hq2, hq1', hq2']
        have hroot : (w.2.2 - w₀.2.2) * (w.2.2 + w₀.2.2) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 hroot with h | h
        · have : w.2.2 = w₀.2.2 := by linear_combination h
          simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          exact Prod.ext hq1 (Prod.ext hq2 this)
        · have : w.2.2 = -w₀.2.2 := by linear_combination h
          simp only [Finset.mem_insert, Finset.mem_singleton]
          right
          exact Prod.ext hq1 (Prod.ext hq2 this)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _ |>.trans (by simp))
  have := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  calc (nullCone p).card ≤ 2 * (Finset.univ : Finset (ZMod p × ZMod p)).card := this
    _ = 2 * p ^ 2 := by
        rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
        ring
