-- Prove2me | Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
-- name    : Speculative_AutoResearch_ThreeSumBirthdayHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:31:24.106216+00:00
-- url     : https://prove2.me/theorems/3353fcad-c9ea-4636-9158-21c434b0db51
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_ThreeSumBirthdayHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.ThreeSumBirthdayHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean by skeleton subtraction
import Mathlib
/-
# The 3SUM / Birthday-Bound Hierarchy for Semiprime Factoring

This file formalises two independent things and then glues them together.

## Part I — the *factor reveal*

If `N = p * q` is a semiprime and `s` is any integer with `p ∣ s` but `q ∤ s`,
then `gcd s N = p`: the hidden factor is revealed exactly.  Applied to a 3SUM
witness `s = a + b + c` this is the "3SUM mod p reveals a factor" observation.
We prove the *complete* classification of `gcd s (p*q)` (four cases) and the
iff-characterisation `gcd s N = p ↔ p ∣ s ∧ ¬ q ∣ s`.

## Part II — the arity-uniform birthday bound

All the collision-based methods (`k` singular-moduli evaluations, `k²` sumset
pairs, `k³` 3SUM triples) are the *same* pigeonhole statement at arity
`r = 1, 2, 3`.  We prove a matching pair of bounds for every arity `r`:

* **sufficiency** `p < C(k,r)` forces a collision (`exists_collision_of_choose_gt`);
* **necessity**  `C(k,r) ≤ p` admits a collision-free instance
  (`threshold_optimal`), hence a *guaranteed* collision costs `> p` enumerated
  tuples, whatever the arity (`guarantee_forces_cost`).

So the arity only changes how the enumerated tuples are packaged: the search set
shrinks (`p < k^r`, so `k > p^{1/r}` — the exponent `1/2 → 1/3` improvement),
but the **net cost stays `> p ≥ √N`** (`sqrt_barrier`).  That is the barrier.

Everything is `sorry`-free.
-/


namespace ThreeSumBirthday

/-! ## Part I : the 3SUM mod-p factor reveal -/

section FactorReveal

variable {p q s : ℕ}







end FactorReveal

/-! ### Verified instance: `N = 143 = 11 * 13`

We enumerate all triples `1 ≤ a < b < c ≤ 11` and count those whose sum is
divisible by `11` (mod-`p`-only) and those divisible by `143` (mod-both). -/

section Instance143

/-- All triples `1 ≤ a < b < c ≤ 11`. -/
def triples11 : List (ℕ × ℕ × ℕ) :=
  ((List.range' 1 11).flatMap fun a =>
    (List.range' 1 11).flatMap fun b =>
      (List.range' 1 11).map fun c => (a, b, c)).filter
    (fun t => decide (t.1 < t.2.1 ∧ t.2.1 < t.2.2))

/-- Triples with `11 ∣ a+b+c`. -/
def modPTriples143 : List (ℕ × ℕ × ℕ) :=
  triples11.filter (fun t => (t.1 + t.2.1 + t.2.2) % 11 == 0)

/-- Triples with `143 ∣ a+b+c` (i.e. mod-`p` *and* mod-`q`). -/
def modBothTriples143 : List (ℕ × ℕ × ℕ) :=
  triples11.filter (fun t => (t.1 + t.2.1 + t.2.2) % 143 == 0)





end Instance143

/-! ## Part II : the arity-uniform birthday bound

We model a "collision search of arity `r` over a set `S`" as the family
`S.powersetCard r` of `r`-element subsets, each evaluated by some residue
function into `ZMod p`.  The canonical evaluation is the subset sum mod `p`. -/

section Birthday

variable {p : ℕ}





end Birthday

/-! ### The hierarchy: the exponent improves, the net cost does not -/

section Hierarchy

variable {p k : ℕ}








end Hierarchy

/-! ## Part III : gluing the two halves — collision ⟹ factor -/

section Pipeline

variable {p q : ℕ}



end Pipeline

end ThreeSumBirthday


