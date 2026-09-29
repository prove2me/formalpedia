-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_lfsr_pref_zero
-- name    : Catalog.Probability.SeedRec.lfsr_pref_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:10:31.131072+00:00
-- url     : https://prove2.me/theorems/93a42d1c-65be-440a-93ce-e3cfdc595edd
-- title:
--   An all-zero seed produces the all-zero file, whatever the taps.
-- statement:
--   An all-zero seed produces the all-zero file, whatever the taps.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.lfsr_pref_zero{L : ℕ} (c : Fin L → K) (n : ℕ) :
--       (lfsrPRNG c).pref n (fun _ => 0) = fun _ => 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGRouterCapacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGRouterCapacity.lean#L187

-- Thm stub generated from Probability/PRNGRouterCapacity.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRouterCapacity
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

open Catalog.Probability.SeedRec

universe u v w

variable {ι : Type u} {α : Type v} [Fintype α] [DecidableEq α]
variable {S : ι → Type w} [∀ i, Fintype (S i)]


variable [Fintype ι] (g : ∀ i, PRNG (S i) α) (n : ℕ)










variable {S₀ S₁ : Type w} [Fintype S₀] [Fintype S₁]







variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K]




omit [Fintype K] [DecidableEq K] in

theorem Catalog.Probability.SeedRec.lfsr_pref_zero{L : ℕ} (c : Fin L → K) (n : ℕ) :
    (lfsrPRNG c).pref n (fun _ => 0) = fun _ => 0 := by sorry
