-- Prove2me | Definitions.Def_Probability_PRNGRouterCapacity
-- name    : Probability_PRNGRouterCapacity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:38.658984+00:00
-- url     : https://prove2.me/theorems/249111a0-d440-44c0-b302-e3883960102b
-- title:
--   Aether Catalog definitions — Probability_PRNGRouterCapacity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGRouterCapacity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGRouterCapacity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# Router capacity: the Kraft-type ceiling for seed compression (conjecture C5)

`Probability.PRNGClassifier` proves a *two-family* no-free-lunch theorem: the
union of the order-`L` LFSR family and the LCG family covers only a vanishing
fraction of files.  This file settles the general statement conjectured as `C5`
in `FUTURE_DIRECTIONS.md`.

A **router** over a finite family of generators is allowed to inspect a file,
choose *any* member of the family, and emit an index together with a seed.  The
theorem below says that its total capacity is exactly the total number of seeds:

```
|{files of length n compressible by some member}| ≤ ∑ i, |S i|.
```

The generators may have *different* state spaces (`S : ι → Type*`), which is the
point: the router is free to mix an LFSR of one order with an LCG with a totally
different state type.  Adding families adds their seed counts and nothing more,
so the "detect the generator" programme buys code space only where the data
distribution is far from uniform — never on average.

Main contents.

* `familyWords` — the files accepted by the router over the family `g`.
* `card_familyWords_le` — **the capacity ceiling** `∑ i, |S i|`.
* `card_not_routed_ge` — a quantitative complement: at least
  `|α|ⁿ - ∑ i, |S i|` files are rejected by *every* member.
* `exists_not_family_routed` — hence, below the ceiling, some file is rejected
  by every member of the family.
* `familyWords_density_le` — the false-positive density of the whole router.
* `card_le_of_family_covers` — the contrapositive: a router that compresses
  *everything* must carry at least `|α|ⁿ` seeds in total, i.e. it saves nothing.
* `exists_not_routed_of_family` — the two-family theorem of
  `PRNGClassifier.lean`, re-derived as the special case `ι = Bool`.
* `card_familyWords_lfsr_lcg_le` — the LFSR ⊎ LCG router as an instance.
-/

namespace Catalog.Probability.SeedRec

universe u v w

variable {ι : Type u} {α : Type v} [Fintype α] [DecidableEq α]
variable {S : ι → Type w} [∀ i, Fintype (S i)]

section Family

variable [Fintype ι] (g : ∀ i, PRNG (S i) α) (n : ℕ)

/-- The files accepted by a router over the finite family of generators `g`:
those reproducible from a seed of *some* member of the family. -/
def familyWords : Finset (Fin n → α) :=
  Finset.univ.biUnion fun i => (g i).compressible n







end Family

section TwoFamilies

variable {S₀ S₁ : Type w} [Fintype S₀] [Fintype S₁]

/-- The state space of a two-element family. -/
def pairState (S₀ S₁ : Type w) : Bool → Type w
  | false => S₀
  | true => S₁

instance instFintypePairState : ∀ b : Bool, Fintype (pairState S₀ S₁ b)
  | false => inferInstanceAs (Fintype S₀)
  | true => inferInstanceAs (Fintype S₁)

/-- A two-element family, packaged so that the general theorem applies. -/
def pairFamily (g₀ : PRNG S₀ α) (g₁ : PRNG S₁ α) :
    ∀ b : Bool, PRNG (pairState S₀ S₁ b) α
  | false => g₀
  | true => g₁


end TwoFamilies

section LFSRRouter

variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K]

/-- The router that tries **every** LFSR order `≤ M` at once: its state space at
order `ℓ` is the pair (taps, seed), of size `|K|^{2ℓ}`. -/
def lfsrFamily (M : ℕ) :
    ∀ i : Fin (M + 1), PRNG ((Fin i.val → K) × (Fin i.val → K)) K :=
  fun _ => { step := fun p => (p.1, lfsrStep p.1 p.2), out := fun p => lfsrOut p.2 }







end LFSRRouter

end Catalog.Probability.SeedRec


