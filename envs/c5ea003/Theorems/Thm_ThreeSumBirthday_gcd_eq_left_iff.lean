-- Prove2me | Theorems.Thm_ThreeSumBirthday_gcd_eq_left_iff
-- name    : ThreeSumBirthday.gcd_eq_left_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:53:29.086331+00:00
-- url     : https://prove2.me/theorems/504eee27-924d-4072-9b4f-0633e5621b37
-- title:
--   The reveal is an exact characterisation, not just a sufficient condition.
-- statement:
--   The reveal is an exact characterisation, not just a sufficient condition.
--
--   ```lean
--   theorem ThreeSumBirthday.gcd_eq_left_iff(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
--       Nat.gcd s (p * q) = p ↔ (p ∣ s ∧ ¬ q ∣ s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean#L86

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

theorem ThreeSumBirthday.gcd_eq_left_iff(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd s (p * q) = p ↔ (p ∣ s ∧ ¬ q ∣ s) := by sorry
