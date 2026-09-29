-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_Prim_applyWord
-- name    : Cryptography.BerggrenModular.Prim_applyWord
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:37:58.932374+00:00
-- url     : https://prove2.me/theorems/59c4a081-066c-4ced-becc-e427bb0e9159
-- title:
--   Prim applyWord
-- statement:
--   Formal statement of `Cryptography.BerggrenModular.Prim_applyWord` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.Prim_applyWord(u : List Move) : Prim (applyWord u root) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/NullCone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/NullCone.lean#L66

-- Thm stub generated from Cryptography/BerggrenModular/NullCone.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
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

theorem Cryptography.BerggrenModular.Prim_applyWord(u : List Move) : Prim (applyWord u root) := by sorry
