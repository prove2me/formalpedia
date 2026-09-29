-- Prove2me | solution 1 for Cryptography.BerggrenModular.lorentz_applyWord
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:08.756505+00:00
-- url     : https://prove2.me/submissions/11dbcadb-f1c9-42ef-bf03-18098a5104e4

-- Sol generated from Cryptography/BerggrenModular/NullCone.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
import Definitions.Def_Cryptography_BerggrenModular_NullCone
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_cons
import Theorems.Thm_Cryptography_BerggrenModular_lorentz_applyMove

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





open Cryptography in
theorem solution(u : List Move) : lorentz (applyWord u root) = 0 := by
  induction u with
  | nil => norm_num [lorentz, root, applyWord]
  | cons i rest ih => rw [applyWord_cons, lorentz_applyMove]; exact ih
