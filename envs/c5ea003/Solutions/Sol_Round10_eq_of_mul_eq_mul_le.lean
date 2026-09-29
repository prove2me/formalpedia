-- Prove2me | solution 1 for Round10.eq_of_mul_eq_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:29.753015+00:00
-- url     : https://prove2.me/submissions/596558f2-fed8-47a8-87e2-2da369bd8d67

-- Sol generated from Geometry/Round10Closures/AggregationCost.lean
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


/-! ### Completeness of the family in the limit -/




/-! ### From completeness to the factorisation -/




/-! ### The cost of completeness: an exponential lower bound on the exponent -/



/-! ### The exact completeness threshold (cycle 4)

The bound `φ(N) ≤ k²` above is not sharp.  The completeness criterion is a divisibility, so
the set of complete exponents is exactly the set of multiples of `lcm(p-1, q-1)`, and the
minimal positive complete exponent is *exactly* `lcm(p-1,q-1) = φ(N) / gcd(p-1,q-1)`.  For
the cryptographically standard case `gcd(p-1,q-1) = 2` this is `φ(N)/2`, i.e. linear in `N`
rather than in `√N`: the true aggregation cost is `Θ(N)`, matching the informal
"O(N) classical aggregation" of the round-10 synthesis. -/






open Round10 in
theorem solution{a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : a * b = A * B) : a = A ∧ b = B := by
  have h1 : a = A := by
    rcases lt_or_eq_of_le ha with hlt | heq
    · exfalso; nlinarith
    · exact heq
  subst h1
  exact ⟨rfl, by
    rcases lt_or_eq_of_le hb with hlt | heq
    · exfalso; nlinarith
    · exact heq⟩
