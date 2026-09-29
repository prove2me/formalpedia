-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_mem_astUniverse
-- name    : ImmuneSystem.PAst.mem_astUniverse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:43:38.149434+00:00
-- url     : https://prove2.me/theorems/a9d8ae6c-e35b-415f-bc0e-284ca806730f
-- title:
--   The bounded code universe is finite.
-- statement:
--   **The bounded code universe is finite.**  Every program of size `â¤ n` whose
--   literals are `< L` occurs in the finite set `astUniverse n L`.
--
--   ```lean
--   theorem ImmuneSystem.PAst.mem_astUniverse(L : ℕ) :
--       ∀ (n : ℕ) (t : PAst), size t ≤ n → litsBelow L t = true → t ∈ astUniverse n L := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneBounded.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneBounded.lean#L60

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

theorem ImmuneSystem.PAst.mem_astUniverse(L : ℕ) :
    ∀ (n : ℕ) (t : PAst), size t ≤ n → litsBelow L t = true → t ∈ astUniverse n L := by sorry
