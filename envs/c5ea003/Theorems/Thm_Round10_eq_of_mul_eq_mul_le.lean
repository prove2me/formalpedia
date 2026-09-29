-- Prove2me | Theorems.Thm_Round10_eq_of_mul_eq_mul_le
-- name    : Round10.eq_of_mul_eq_mul_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:54.931377+00:00
-- url     : https://prove2.me/theorems/5bb95317-0321-4ea6-9ed6-133b3da47ac4
-- title:
--   Cancellation for a product of two coordinates each bounded by its maximum: if the
-- statement:
--   Cancellation for a product of two coordinates each bounded by its maximum: if the
--   product is maximal, both coordinates are.
--
--   ```lean
--   theorem Round10.eq_of_mul_eq_mul_le{a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
--       (h : a * b = A * B) : a = A ∧ b = B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/AggregationCost.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/AggregationCost.lean#L25

-- Thm stub generated from Geometry/Round10Closures/AggregationCost.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_HintAmplification
/-
Round-10 Closures — Part VII (cycle 2): the quantitative cost of aggregation.

Cycle 1 showed that *finite* joints of free witnesses never close (barrier 4).  Cycle 2 asks
the sharper, quantitative question: the family `R_k` is complete in the limit — at
`k = lcm(p-1, q-1)` the witness equals `φ(N)`, and `φ(N)` together with `N` recovers the
factorisation in closed form.  So what does completeness *cost*?

The answer proved here is a genuine exponential separation inside the classical channel:

* **completeness**: `R_k(N) = φ(N)` exactly when `(p-1) ∣ k` and `(q-1) ∣ k`, and then the
  factorisation is read off by `factorFromTrace N (N - R_k + 1)`;
* **cost**: since `R_k ∣ k²`, any *positive* exponent with a complete witness satisfies
  `φ(N) ≤ k²`, i.e. `k ≥ √φ(N) ≈ √N` — exponential in `log N`.

Together: the free-witness channel is complete but only at exponents of size `√N`, which is
precisely the "aggregation necessity" content of barrier 4, and precisely what the quantum
order-finding channel bypasses (it reads the coordinate off one superposition).
-/

open Round10

variable {p q k : ℕ}

theorem Round10.eq_of_mul_eq_mul_le{a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : a * b = A * B) : a = A ∧ b = B := by sorry
