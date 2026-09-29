-- Prove2me | solution 1 for FreeWitness.comp_eq_of_witness_poly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:27:46.516066+00:00
-- url     : https://prove2.me/submissions/30d9066b-6fbd-4227-b700-38a07529617b

-- Sol generated from MachineLearning/FreeWitnessClassification.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessTraceLemma

/-!
# The classification theorem for power-shaped free witnesses

Cycle 2.  `FreeWitnessTraceLemma.lean` isolated the abstract mechanism; this file proves
the two halves of the classification *simultaneously and in general*, for every witness
whose local weight has the affine-power shape `w x = a x^k + c`:

* **Factoring-completeness** (`SemiprimeWitness.affinePower_recovery`): the aggregate
  determines the power sum `p^k + q^k`, hence — through the three recovery channels
  below — the factorisation.

* **Non-polynomiality** (`powerWeight_not_polynomial`): for `k ≥ 1` and `c ≠ 0` no
  integer polynomial in `N` agrees with the aggregate on all odd semiprimes.  This is a
  rigidity theorem, proved from the infinitude of primes: fixing one prime `r` forces
  `P(r X) = (r^k + c)(X^k + c)` as an identity of polynomials, and the two evaluations
  `P(3 · 10) = P(5 · 6)` then collide, because `10^k + 3^k ≠ 6^k + 5^k` for `k ≥ 1`.
  So a *non-polynomial local weight forces a non-polynomial aggregate* — the exact
  implication asserted, but not proved, in the source paper.

* **The three recovery channels of the trace lemma** (§2 of the paper) are all shown to
  be complete: `two_mul_max_eq` (trace ⇒ `max(p,q)`), `factor_of_max` (`max` ⇒ the other
  factor), `residue_channel` (a residue vector modulo a large enough modulus ⇒ the
  factor).  Together with `pair_determined_of_sum_prod` this is the statement that the
  information content of a recoverable witness is exactly one factor-secret coordinate.

* `classification_of_powerWeight` packages both halves into a single statement.
-/

open FreeWitness

open Polynomial

/-! ## Affine-power local weights: recovery -/

open SemiprimeWitness

variable (F : SemiprimeWitness)



/-! ## The three recovery channels -/




/-! ## Non-polynomiality of every power-shaped witness -/






/-! ### Lab notes (cycle 2)

Rigidity evaluation table (the two candidate values of `P(30)`), for the local weight
`x^k + c`:

```
k :  1        2         3           c-coefficient identity forced
     (3+c)(10+c) = (5+c)(6+c)   →  13c = 11c   → c = 0
     (9+c)(100+c) = (25+c)(36+c) → 109c = 61c  → c = 0
     (27+c)(1000+c) = (125+c)(216+c) → 1027c = 341c → c = 0
```
In every case `10^k + 3^k > 6^k + 5^k`, so `c = 0`: a non-trivial constant term in the
local weight is incompatible with a polynomial closed form in `N`.
-/

example : (10 : ℕ) ^ 1 + 3 ^ 1 ≠ 6 ^ 1 + 5 ^ 1 := by norm_num

example : (10 : ℕ) ^ 3 + 3 ^ 3 ≠ 6 ^ 3 + 5 ^ 3 := by norm_num


open FreeWitness in
theorem solution(F : SemiprimeWitness) {k : ℕ} {c : ℤ}
    (hw : ∀ s : ℕ, s.Prime → s ≠ 2 → F.w s = (s : ℤ) ^ k + c)
    {P : Polynomial ℤ}
    (hP : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
      F.W (p * q) = P.eval ((p : ℤ) * q))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    P.comp (C (r : ℤ) * X) = C ((r : ℤ) ^ k + c) * (X ^ k + C c) := by
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  have hS : ({q : ℕ | q.Prime} \ {r, 2}).Infinite :=
    Nat.infinite_setOf_prime.diff (Set.toFinite {r, 2})
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ)) ({q : ℕ | q.Prime} \ {r, 2}) := by
    intro a _ b _ hab
    simpa using hab
  refine (hS.image hinj).mono ?_
  rintro x ⟨q, hq, rfl⟩
  have hqp : q.Prime := hq.1
  have hq2 : q ≠ 2 := fun h => hq.2 (by simp [h])
  have hqr : r ≠ q := fun h => hq.2 (by simp [h])
  have hval : F.W (r * q) = P.eval ((r : ℤ) * q) := hP r q hr hqp hr2 hq2 hqr
  have hloc : F.W (r * q) = F.w r * F.w q := F.factorizes hr hqp hr2 hq2 hqr
  simp only [Set.mem_setOf_eq, eval_comp, eval_mul, eval_add, eval_pow, eval_C, eval_X]
  rw [← hval, hloc, hw r hr hr2, hw q hqp hq2]
