-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_pref_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:20:03.134061+00:00
-- url     : https://prove2.me/submissions/8b870828-7f66-437c-a713-410e4e4ed211

-- Sol generated from Probability/PRNGRouterCapacity.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_PRNG_stream_succ

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










open Catalog.Probability.SeedRec in
omit [Fintype K] [DecidableEq K] in
theorem solution{L : ℕ} (c : Fin L → K) (n : ℕ) :
    (lfsrPRNG c).pref n (fun _ => 0) = fun _ => 0 := by
  have hstream : ∀ t : ℕ, (lfsrPRNG c).stream (fun _ => 0) t = 0 := by
    intro t
    induction t with
    | zero => simp [PRNG.stream, lfsrPRNG, lfsrOut]
    | succ t ih =>
        rw [PRNG.stream_succ]
        have hstep : (lfsrPRNG c).step (fun _ => 0) = fun _ : Fin L => (0 : K) := by
          funext j
          simp [lfsrPRNG, lfsrStep]
        rw [hstep]
        exact ih
  funext j
  exact hstream (j : ℕ)
