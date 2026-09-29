-- Prove2me | Theorems.Thm_ThreeSumBirthday_choose_three_mul_six_le
-- name    : ThreeSumBirthday.choose_three_mul_six_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:53:09.609583+00:00
-- url     : https://prove2.me/theorems/01575308-c071-4089-be49-3b1377d280c6
-- title:
--   `6 · C(n,3) ≤ n³`, proved by induction via Pascal's rule.
-- statement:
--   `6 · C(n,3) ≤ n³`, proved by induction via Pascal's rule.
--
--   ```lean
--   theorem ThreeSumBirthday.choose_three_mul_six_le: ∀ n : ℕ, n.choose 3 * 6 ≤ n * n * n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/ThreeSumBirthdayHierarchy.lean#L254

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








/-! ### Verified instance: `N = 143 = 11 * 13`

We enumerate all triples `1 ≤ a < b < c ≤ 11` and count those whose sum is
divisible by `11` (mod-`p`-only) and those divisible by `143` (mod-both). -/










/-! ## Part II : the arity-uniform birthday bound

We model a "collision search of arity `r` over a set `S`" as the family
`S.powersetCard r` of `r`-element subsets, each evaluated by some residue
function into `ZMod p`.  The canonical evaluation is the subset sum mod `p`. -/


variable {p : ℕ}






/-! ### The hierarchy: the exponent improves, the net cost does not -/


variable {p k : ℕ}

theorem ThreeSumBirthday.choose_three_mul_six_le: ∀ n : ℕ, n.choose 3 * 6 ≤ n * n * n := by sorry
