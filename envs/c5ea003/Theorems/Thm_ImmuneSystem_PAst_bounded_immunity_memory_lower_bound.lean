-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_bounded_immunity_memory_lower_bound
-- name    : ImmuneSystem.PAst.bounded_immunity_memory_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:43:07.515517+00:00
-- url     : https://prove2.me/theorems/f734763b-ccb6-4d6b-bfd7-1723150ce0f9
-- title:
--   The price of perfect immunity: exponential memory.
-- statement:
--   **The price of perfect immunity: exponential memory.**  Whenever the size
--   bound `N` admits the `n`-bit family of behaviourally trivial programs, the
--   bounded whitelist has at least `2 ^ n` entries.  Perfect immunity on a universe
--   of size bound `N` therefore costs about `2 ^ (N / 3)` attestation tags.
--
--   ```lean
--   theorem ImmuneSystem.PAst.bounded_immunity_memory_lower_bound{N L n : ℕ} (hL : 2 ≤ L) (hN : 3 * n + 1 ≤ N) :
--       2 ^ n ≤ (boundedWhitelist N L).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneBounded.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneBounded.lean#L157

-- Thm stub generated from Shared/ImmuneBounded.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneEnsemble

/-!
# Algorithmic Immune System, Part VIII: bounded universes — perfect immunity and its price

Parts III, V and VII are impossibility results; Part IV gives containment at the
price of rigidity.  This part identifies the regime in which the algorithmic
immune system is *provably perfect*, and computes the price exactly.

Fix a size bound `N` and a literal bound `L`.  The programs of size `≤ N` whose
literals are `< L` form a finite universe (`mem_astUniverse`), so the monitor can
whitelist **all** benign programs of that universe:

* `bounded_perfect_immunity` — there is a whitelist `S` with
  * containment: every sanctioned program is harmless, hence by Part IV no
    adversary ever triggers the forbidden action, and
  * *zero false positives inside the universe*: every harmless program of the
    universe is accepted.
* `bounded_immunity_memory_lower_bound` — but any such whitelist has at least
  `2 ^ n` entries whenever `3n + 1 ≤ N` and `2 ≤ L`; i.e. its memory is
  exponential in the size bound, `2 ^ ((N-1)/3)`.

So perfect algorithmic immunity is attainable exactly on bounded code universes,
and the attestation database must then be exponentially large: the impossibility
results of Parts III/V/VII are the `N → ∞` limit of this trade-off.
-/

open ImmuneSystem
open PAst

open Finset

theorem ImmuneSystem.PAst.bounded_immunity_memory_lower_bound{N L n : ℕ} (hL : 2 ≤ L) (hN : 3 * n + 1 ≤ N) :
    2 ^ n ≤ (boundedWhitelist N L).card := by sorry
