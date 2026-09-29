-- Prove2me | solution 1 for Cryptography.BerggrenModular.stateMod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:29:32.166225+00:00
-- url     : https://prove2.me/submissions/2f8b9274-d31c-4f58-85f7-4bde4e25c049

-- Sol generated from Cryptography/BerggrenModular/NullCone.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Definitions.Def_Cryptography_BerggrenModular_NullCone
import Theorems.Thm_Cryptography_BerggrenModular_Prim_applyWord

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
theorem solution(p : ℕ) [hp : Fact (Nat.Prime p)] (u : List Move) :
    stateMod p u ≠ (0, 0, 0) := by
  intro hEq
  rw [stateMod, redTri, Prod.mk.injEq, Prod.mk.injEq] at hEq
  obtain ⟨h1, h2, h3⟩ := hEq
  have d1 : (p : ℤ) ∣ (applyWord u root).1 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have d2 : (p : ℤ) ∣ (applyWord u root).2.1 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have d3 : (p : ℤ) ∣ (applyWord u root).2.2 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := Prim_applyWord u (p : ℤ) d1 d2 d3
  rw [Int.isUnit_iff] at this
  have h2' : 2 ≤ p := hp.out.two_le
  omega
