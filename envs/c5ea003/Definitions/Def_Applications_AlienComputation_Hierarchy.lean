-- Prove2me | Definitions.Def_Applications_AlienComputation_Hierarchy
-- name    : Applications_AlienComputation_Hierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:43.490965+00:00
-- url     : https://prove2.me/theorems/c941848a-cc25-462f-aaa1-0e1feb2fd905
-- title:
--   Aether Catalog definitions — Applications_AlienComputation_Hierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AlienComputation.Hierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AlienComputation/Hierarchy.lean by skeleton subtraction
import Mathlib

/-!
# A universal, substrate-independent complexity hierarchy

**Research theme: Computational Complexity of Alien Civilizations.**

The diagonal argument (`Lawvere.lean`, `Uncomputability.lean`) shows that the
space of decision behaviours on a type is strictly richer than the type itself.
Iterating this one step at a time produces an **infinite strictly increasing
tower** of "decision-power levels":

`Level 0 = A`,  `Level (n+1) = Level n → Bool`.

Each level is the set of Boolean decision procedures over the previous one — the
"problems about problems about … about `A`".  We prove:

* there is a canonical **embedding** of each level into the next
  (`Hierarchy.embeds`), so power never decreases; and
* there is **no surjection** from a level onto the next
  (`Hierarchy.no_surjection`), so power strictly increases at every step
  (`Hierarchy.strict_step`); equivalently the **cardinalities strictly
  increase** (`Hierarchy.mk_lt`).

Because the construction and both proofs are pure function theory — no machine
model, no physics — this hierarchy is forced on *every* civilization: it is a
universal complexity hierarchy.  In particular there is **no maximal level**
(`Hierarchy.no_maximal`): whatever decision-power a civilization attains, a
strictly greater level provably exists.
-/

namespace AlienComputation
namespace Hierarchy

universe u

variable (A : Type u)

/-- The tower of decision-power levels over a base type `A`:
`Level 0 = A` and `Level (n+1) = (Level n → Bool)`, the decision procedures over
level `n`. -/
def Level : ℕ → Type u
  | 0 => A
  | n + 1 => Level n → Bool











end Hierarchy
end AlienComputation


