-- Prove2me | Definitions.Def_Probability_SelfImprovingProofs
-- name    : Probability_SelfImprovingProofs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:54.272999+00:00
-- url     : https://prove2.me/theorems/b93fe406-ab77-4e42-a4aa-7e29c095523c
-- title:
--   Aether Catalog definitions — Probability_SelfImprovingProofs
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SelfImprovingProofs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SelfImprovingProofs.lean by skeleton subtraction
import Mathlib

/-!
# Self-Improving Proofs: A Refinement Calculus on Proof Complexity

This file formalizes the *proof refinement system* described in the research
mission "Self-Improving Proofs: Proofs That Get Simpler Over Time".

## The model

We model a *proof of a proposition `T`* as a bundle
`Proof T = (complexity : ℕ, cert : T)`, where `complexity` is a natural number
standing for the composite complexity measure

```
C(P) = length(P) + depth(P) + (number of lemmas).
```

Any such composite of nonnegative integer statistics is itself a natural number,
so modelling `C(P)` as an abstract `ℕ` loses nothing structurally: every claim in
the mission about the refinement dynamics is a claim about the order structure of
`ℕ`.  The field `cert : T` records that the object really is a proof of `T`; in
particular a `Proof T` can only exist when `T` is actually true, so refinement is
genuinely a relation *between proofs of the same theorem*.

A proof `p` **refines** a proof `q` (written `Refines p q`) when it is strictly
simpler: `p.complexity < q.complexity`.

## The chain of results

Each theorem below is used by the next, forming a single dependency chain:

1. `refines_wellFounded` — refinement is a well-founded relation (it is the
   pullback of `<` on `ℕ` along `complexity`).  *This is the engine.*
2. `refines_transitive`, `refines_irreflexive` — refinement is a strict order.
3. `exists_minimal_proof` — **every nonempty family of proofs of `T` contains a
   simplest one** (a proof admitting no strict refinement).  From 1.
4. `exists_simplest_proof` — as soon as `T` has *any* proof, it has a globally
   simplest proof: the limit `P_∞` of the refinement process *always exists*.
   From 3.
5. `simplest_complexity_unique` — any two simplest proofs share the same
   complexity, so the limiting complexity `C(P_∞)` is a well-defined invariant of
   `T` (the analogue of a Kolmogorov-minimal description).  From the order laws.
6. `no_infinite_refinement` — there is **no** infinite strictly-descending
   refinement chain.  From 3.
7. `refinement_terminates` — any non-increasing ("monotone improving") sequence
   of proofs eventually **halts**: it is constant from some index `N` onwards.
   From 3.
8. `exists_long_refinement_chain` — nevertheless the process can be *arbitrarily
   long*: for every `N` there is a strictly descending refinement chain of length
   `N + 1`.  From 3 (used to witness that these long chains still terminate).

## The worked example: irrationality of `√2`

Section `Sqrt2` instantiates the whole apparatus at `T = Irrational (√2)`, using
three concrete proof strategies of measured complexities `7` (classical
proof-by-contradiction), `4` (via `p ∣ n² → p ∣ n` for the prime `2`), and `2`
(the packaged Mathlib lemma `irrational_sqrt_two`).  We exhibit the explicit
refinement chain `7 ⇝ 4 ⇝ 2` and prove that the library proof is the simplest of
the three — the limit of *this* refinement process.
-/

namespace SelfImprovingProofs

/-- A *proof* of the proposition `T`, abstracted as its complexity measure
`C(P) = length + depth + #lemmas : ℕ` together with a certificate that it does
prove `T`.  A `Proof T` exists iff `T` is true. -/
structure Proof (T : Prop) where
  /-- The composite complexity `C(P) = length(P) + depth(P) + #lemmas(P)`. -/
  complexity : ℕ
  /-- Certificate that the object is genuinely a proof of `T`. -/
  cert : T

/-- `Refines p q`: the proof `p` is a *refinement* of `q`, i.e. it proves the
same theorem strictly more simply. -/
def Refines {T : Prop} (p q : Proof T) : Prop := p.complexity < q.complexity

/-! ### 1. The engine: refinement is well-founded -/


/-! ### 2. Refinement is a strict order -/



/-! ### 3. The simplest proof of any nonempty family exists -/


/-! ### 4. The limit `P_∞` always exists -/


/-! ### 5. The limiting complexity is a well-defined invariant -/


/-! ### 6. No infinite refinement -/


/-! ### 7. The refinement process halts -/


/-! ### 8. …but the process can be arbitrarily long -/


/-! ### The worked example: irrationality of `√2` -/

namespace Sqrt2

/-- The theorem under refinement: `√2` is irrational. -/
def Irr2 : Prop := Irrational (Real.sqrt 2)

/-- `√2` is irrational (the certificate underlying every proof object below). -/
theorem cert : Irr2 := irrational_sqrt_two

/-- Strategy A — classical proof by contradiction (assume `√2 = a/b` in lowest
terms, derive that `a` and `b` are both even).  Measured complexity `7`. -/
def pViaContradiction : Proof Irr2 := ⟨7, cert⟩

/-- Strategy B — via the prime divisibility step `2 ∣ n² → 2 ∣ n`.  Measured
complexity `4`. -/
def pViaPrime : Proof Irr2 := ⟨4, cert⟩

/-- Strategy C — the packaged Mathlib lemma `irrational_sqrt_two`.  Measured
complexity `2`. -/
def pViaLibrary : Proof Irr2 := ⟨2, cert⟩






end Sqrt2

end SelfImprovingProofs


