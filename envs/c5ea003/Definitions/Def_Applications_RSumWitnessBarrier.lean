-- Prove2me | Definitions.Def_Applications_RSumWitnessBarrier
-- name    : Applications_RSumWitnessBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:49.574978+00:00
-- url     : https://prove2.me/theorems/6a91e614-8c68-4cab-a458-e8148c2c9e3c
-- title:
--   Aether Catalog definitions — Applications_RSumWitnessBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.RSumWitnessBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/RSumWitnessBarrier.lean by skeleton subtraction
import Mathlib
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

namespace RSumWitnessBarrier

open Finset

/-- Tuples of the search box: `r` positive entries, each at most `K`. -/
def InBox (K : ℕ) {r : ℕ} (x : Fin r → ℕ) : Prop := ∀ i, 0 < x i ∧ x i ≤ K






end RSumWitnessBarrier


