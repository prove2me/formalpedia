-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_NullCone
-- name    : Cryptography_BerggrenModular_NullCone
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:09:19.224176+00:00
-- url     : https://prove2.me/theorems/17fdf64f-eace-43a4-9721-d34a7ad0e9d3
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_NullCone
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.NullCone`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/NullCone.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
import Definitions.Def_Cryptography_BerggrenModular_Modular

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

namespace Cryptography
namespace BerggrenModular

/-! ## Primitivity -/

/-- A triple is primitive when its three entries have no common non-unit divisor. -/
def Prim (v : Tri) : Prop := ∀ d : ℤ, d ∣ v.1 → d ∣ v.2.1 → d ∣ v.2.2 → IsUnit d




/-! ## The observation lies on the punctured null cone -/




/-! ## Counting the null cone modulo a prime -/

/-- The null cone modulo `m`, as a finite set of states. -/
def nullCone (m : ℕ) [NeZero m] : Finset (TriM m) :=
  Finset.univ.filter (fun w => lorentzM m w = 0)



/-! ## Sharpened ambiguity -/




end BerggrenModular
end Cryptography


