-- Prove2me | Definitions.Def_Shared_ImmuneBounded
-- name    : Shared_ImmuneBounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:02:02.277786+00:00
-- url     : https://prove2.me/theorems/7223eee9-69dc-4bfb-9a0d-79d6db92b4d3
-- title:
--   Aether Catalog definitions — Shared_ImmuneBounded
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneBounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneBounded.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneEnsemble
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

namespace ImmuneSystem
namespace PAst

open Finset

/-- All literals occurring in the program are `< L`. -/
def litsBelow (L : ℕ) : PAst → Bool
  | inp => true
  | attack => true
  | lit n => decide (n < L)
  | ite c a b => litsBelow L c && litsBelow L a && litsBelow L b
  | call f a => litsBelow L f && litsBelow L a


/-- A finite over-approximation of the programs of size `≤ n` with literals
`< L`.  (Over-approximation is harmless: all we need is that it *contains* the
bounded universe, which makes the latter finite.) -/
def astUniverse : ℕ → ℕ → Finset PAst
  | 0, _ => ∅
  | n + 1, L =>
      insert inp (insert attack
        (((Finset.range L).image lit) ∪
          ((((astUniverse n L) ×ˢ (astUniverse n L)) ×ˢ (astUniverse n L)).image
            (fun p => ite p.1.1 p.1.2 p.2)) ∪
          (((astUniverse n L) ×ˢ (astUniverse n L)).image (fun p => call p.1 p.2))))


/-- The immune system's whitelist for the bounded universe: every harmless
program of size `≤ N` with literals `< L`. -/
def BoundedOk (N L : ℕ) (t : PAst) : Prop :=
  size t ≤ N ∧ litsBelow L t = true ∧ run t = false

instance (N L : ℕ) : DecidablePred (BoundedOk N L) := fun t => by
  unfold BoundedOk; infer_instance

def boundedWhitelist (N L : ℕ) : Finset PAst := (astUniverse N L).filter (BoundedOk N L)






end PAst
end ImmuneSystem


