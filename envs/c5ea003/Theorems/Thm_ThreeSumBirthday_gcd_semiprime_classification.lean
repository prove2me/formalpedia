-- Prove2me | Theorems.Thm_ThreeSumBirthday_gcd_semiprime_classification
-- name    : ThreeSumBirthday.gcd_semiprime_classification
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:53:41.391978+00:00
-- url     : https://prove2.me/theorems/1d587f9a-5ff3-43cf-96ee-f1a2ec86ffcb
-- title:
--   Complete classification of `gcd s (p*q)` for distinct primes `p ≠ q`:
-- statement:
--   Complete classification of `gcd s (p*q)` for distinct primes `p ≠ q`:
--   it is `1`, `p`, `q` or `p*q` according to which primes divide `s`.
--
--   ```lean
--   theorem ThreeSumBirthday.gcd_semiprime_classification(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
--       Nat.gcd s (p * q) =
--         if p ∣ s then (if q ∣ s then p * q else p) else (if q ∣ s then q else 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean#L64

-- Thm stub generated from Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
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


open ThreeSumBirthday

/-! ## Part I : the 3SUM mod-p factor reveal -/


variable {p q s : ℕ}

theorem ThreeSumBirthday.gcd_semiprime_classification(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd s (p * q) =
      if p ∣ s then (if q ∣ s then p * q else p) else (if q ∣ s then q else 1) := by sorry
