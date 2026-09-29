-- Prove2me | Theorems.Thm_FreeWitness_comp_eq_of_witness_poly
-- name    : FreeWitness.comp_eq_of_witness_poly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:20:48.735093+00:00
-- url     : https://prove2.me/theorems/86cc9afc-7a3d-43b2-8f23-453f72f48fc7
-- title:
--   Rigidity.
-- statement:
--   **Rigidity.**  If some integer polynomial computes the aggregate on all odd
--   semiprimes, then fixing one odd prime `r` and letting the other prime run over the
--   infinitely many remaining primes forces the *polynomial identity*
--   `P(r X) = (r^k + c)(X^k + c)`.
--
--   ```lean
--   theorem FreeWitness.comp_eq_of_witness_poly(F : SemiprimeWitness) {k : ℕ} {c : ℤ}
--       (hw : ∀ s : ℕ, s.Prime → s ≠ 2 → F.w s = (s : ℤ) ^ k + c)
--       {P : Polynomial ℤ}
--       (hP : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
--         F.W (p * q) = P.eval ((p : ℤ) * q))
--       {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
--       P.comp (C (r : ℤ) * X) = C ((r : ℤ) ^ k + c) * (X ^ k + C c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/FreeWitnessClassification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/FreeWitnessClassification.lean#L104

-- Thm stub generated from MachineLearning/FreeWitnessClassification.lean
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

theorem FreeWitness.comp_eq_of_witness_poly(F : SemiprimeWitness) {k : ℕ} {c : ℤ}
    (hw : ∀ s : ℕ, s.Prime → s ≠ 2 → F.w s = (s : ℤ) ^ k + c)
    {P : Polynomial ℤ}
    (hP : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
      F.W (p * q) = P.eval ((p : ℤ) * q))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    P.comp (C (r : ℤ) * X) = C ((r : ℤ) ^ k + c) * (X ^ k + C c) := by sorry
