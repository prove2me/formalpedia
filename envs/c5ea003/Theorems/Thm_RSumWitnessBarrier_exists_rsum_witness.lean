-- Prove2me | Theorems.Thm_RSumWitnessBarrier_exists_rsum_witness
-- name    : RSumWitnessBarrier.exists_rsum_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:55.506118+00:00
-- url     : https://prove2.me/theorems/548b830a-46a5-496a-9326-f109269e8e67
-- title:
--   Above the threshold a witness always exists: an explicit greedy tuple whose
-- statement:
--   Above the threshold a witness always exists: an explicit greedy tuple whose
--   entries lie in `[1,K]` and whose sum is exactly `p`.
--
--   ```lean
--   theorem RSumWitnessBarrier.exists_rsum_witness: ∀ {p K r : ℕ}, 1 ≤ r → r ≤ p → p ≤ r * K →
--       ∃ x : Fin r → ℕ, InBox K x ∧ ∑ i, x i = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/RSumWitnessBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/RSumWitnessBarrier.lean#L49

-- Thm stub generated from Applications/RSumWitnessBarrier.lean
import Mathlib
import Definitions.Def_Applications_RSumWitnessBarrier
/-
# The `r`-SUM witness barrier: arity never compresses the search box

Fourth cycle.  `Catalog/Applications/ThreeSumSearchSpace.lean` proved, for arity
`3`, that a witness with positive entries bounded by `K` exists **iff** `p ≤ 3K`.
The obvious hypothesis — raised as a conjecture at the end of cycle 3 — is that
the same dichotomy holds at every arity `r`, with threshold `p ≤ r·K`.  Here it
is proved.

* `no_rsum_witness_of_small` : if `r·K < p` no `r`-tuple in the box `[1,K]^r`
  has sum divisible by `p`;
* `exists_rsum_witness` : if `r ≤ p ≤ r·K` (and `r ≥ 1`) such a tuple exists,
  by an explicit greedy construction (induction on `r` using `Fin.cons`);
* `rsum_witness_iff` : the exact dichotomy;
* `rsum_entry_size_barrier` : consequently, for a balanced semiprime `N = p*q`
  with `q ≤ 2p`, any arity-`r` search box that contains a witness obeys
  `N ≤ 2·r²·K²`, i.e. `K ≥ √N / (r√2)`.

Interpretation: increasing the arity shrinks the required entry magnitude only
by the *linear* factor `r`, never polynomially.  Combined with
`BirthdayBoundHierarchy.birthday_barrier_sqrt` (the number of inspected
selections must exceed `p` at every arity) both axes of the hierarchy are now
pinned: neither the count nor the magnitude improves past `√N`.
-/

open RSumWitnessBarrier

open Finset

theorem RSumWitnessBarrier.exists_rsum_witness: ∀ {p K r : ℕ}, 1 ≤ r → r ≤ p → p ≤ r * K →
    ∃ x : Fin r → ℕ, InBox K x ∧ ∑ i, x i = p := by sorry
