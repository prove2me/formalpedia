-- Prove2me | Theorems.Thm_Novelty_NoPinning_fullBattery_isModObs
-- name    : Novelty.NoPinning.fullBattery_isModObs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:41.28913+00:00
-- url     : https://prove2.me/theorems/7c2b4e44-7cc3-4c02-a0fb-8d97d197b07e
-- title:
--   FullBattery isModObs
-- statement:
--   Formal statement of `Novelty.NoPinning.fullBattery_isModObs` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Novelty.NoPinning.fullBattery_isModObs(B : ℕ) :
--       ∀ f ∈ fullBattery B, IsModObs (modLevel B) f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningBattery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningBattery.lean#L95

-- Thm stub generated from Novelty/NoPinningBattery.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningBattery
import Definitions.Def_Novelty_NoPinningLemma
/-
# The poly(log N) battery: residues, Jacobi symbols and gcds

Companion to `Novelty/NoPinningLemma.lean`.  Here we exhibit the concrete
`poly(log N)`-computable battery of the COMPENSATING-PARTNER experiment as a
family of modulus-`L` observables, with `L = modLevel B = 4 · lcm(1,…,B)`:

* `residueObs m : N ↦ N mod m` for `1 ≤ m ≤ B`,
* `jacobiObs a : N ↦ (a | N)` (Jacobi symbol) for `1 ≤ a ≤ B`,
* `gcdObs c : N ↦ gcd(N, c)` for `1 ≤ c ≤ B`.

and we prove:

* `isModObs_residueObs`, `isModObs_jacobiObs`, `isModObs_gcdObs` — each channel
  is a modulus-`L` observable;
* `fullBattery_no_pinning` — the entire battery is blind: for every target `N₀`
  and every candidate prime `p` coprime to `L` there are infinitely many primes
  `q` with identical battery readouts on `p·q` and `N₀`;
* `prime_dvd_modLevel_iff` — the pinned primes at level `B` are exactly the
  primes `≤ B` (plus `2`), so `card ≤ B`: `poly(log N)` many;
* `large_prime_never_pinned` — every prime candidate `p > B` survives;
* `Int.gcd_eval_eq_gcd_coeff_zero` — **barrier 1**: `gcd(f(N), N) = gcd(f(0), N)`
  for every integer polynomial `f`; polynomial gcds are functions of `N` alone
  and add no pinning power.  In particular `gcd(N + k, N) = gcd(k, N)`.
-/


open Novelty.NoPinning

/-! ## The modulus of a level-`B` battery -/






instance (B : ℕ) : NeZero (modLevel B) := ⟨modLevel_ne_zero B⟩



/-! ## The three observable channels -/

theorem Novelty.NoPinning.fullBattery_isModObs(B : ℕ) :
    ∀ f ∈ fullBattery B, IsModObs (modLevel B) f := by sorry
