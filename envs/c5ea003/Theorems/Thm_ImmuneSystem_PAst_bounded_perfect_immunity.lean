-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_bounded_perfect_immunity
-- name    : ImmuneSystem.PAst.bounded_perfect_immunity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:44:09.84643+00:00
-- url     : https://prove2.me/theorems/6a2442fd-47cb-48be-b916-d6dd41b14e98
-- title:
--   Perfect immunity on a bounded universe.
-- statement:
--   **Perfect immunity on a bounded universe.**  The bounded whitelist contains
--   the trusted baseline, contains *only* harmless programs (so by Part IV no
--   adversary, however unknown or self-modifying, ever triggers the forbidden
--   action), and rejects *no* harmless program of the universe: zero false
--   positives.
--
--   ```lean
--   theorem ImmuneSystem.PAst.bounded_perfect_immunity{N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
--       lit 0 ∈ boundedWhitelist N L ∧
--         (∀ t ∈ boundedWhitelist N L, ¬ malicious t) ∧
--         (∀ t : PAst, size t ≤ N → litsBelow L t = true → ¬ malicious t →
--           t ∈ boundedWhitelist N L) ∧
--         (∀ (adv : ℕ → PAst → PAst) (k : ℕ),
--           ¬ malicious (trace (boundedWhitelist N L) (lit 0) adv k)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneBounded.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneBounded.lean#L123

-- Thm stub generated from Shared/ImmuneBounded.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneEnsemble
import Definitions.Def_Shared_ImmuneQuarantine
import Definitions.Def_Shared_ImmuneSemantics

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

theorem ImmuneSystem.PAst.bounded_perfect_immunity{N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    lit 0 ∈ boundedWhitelist N L ∧
      (∀ t ∈ boundedWhitelist N L, ¬ malicious t) ∧
      (∀ t : PAst, size t ≤ N → litsBelow L t = true → ¬ malicious t →
        t ∈ boundedWhitelist N L) ∧
      (∀ (adv : ℕ → PAst → PAst) (k : ℕ),
        ¬ malicious (trace (boundedWhitelist N L) (lit 0) adv k)) := by sorry
