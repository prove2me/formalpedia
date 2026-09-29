-- Prove2me | solution 1 for Catalog.Probability.SeedRec.familyWords_lfsrFamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:34:41.406687+00:00
-- url     : https://prove2.me/submissions/cd87f4d4-6944-4354-9c54-c9bd249d8378

-- Sol generated from Probability/PRNGRouterCapacity.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_PRNG_mem_compressible
import Theorems.Thm_Catalog_Probability_SeedRec_PRNG_stream_succ
import Theorems.Thm_Catalog_Probability_SeedRec_lfsrWords_monotone
import Theorems.Thm_Catalog_Probability_SeedRec_lfsr_pref_zero
import Theorems.Thm_Catalog_Probability_SeedRec_mem_lfsrWords

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


omit [Fintype α] in
theorem mem_familyWords {x : Fin n → α} :
    x ∈ familyWords g n ↔ ∃ i, SeedCompressible (g i) n x := by
  simp [familyWords]








variable {S₀ S₁ : Type w} [Fintype S₀] [Fintype S₁]







variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K]


omit [Fintype K] [DecidableEq K] in
/-- The family member of order `ℓ` runs the ordinary LFSR: it carries its taps
along unchanged, so its stream is the stream of `lfsrPRNG`. -/
theorem lfsrFamily_stream (M : ℕ) (i : Fin (M + 1)) (c σ : Fin i.val → K) (t : ℕ) :
    ((lfsrFamily K M) i).stream (c, σ) t = (lfsrPRNG c).stream σ t := by
  induction t generalizing σ with
  | zero => rfl
  | succ t ih =>
      rw [PRNG.stream_succ, PRNG.stream_succ]
      exact ih _

omit [Fintype K] [DecidableEq K] in
theorem lfsrFamily_pref (M : ℕ) (i : Fin (M + 1)) (c σ : Fin i.val → K) (n : ℕ) :
    ((lfsrFamily K M) i).pref n (c, σ) = (lfsrPRNG c).pref n σ := by
  funext j
  exact lfsrFamily_stream K M i c σ (j : ℕ)







open Catalog.Probability.SeedRec in
theorem solution(M n : ℕ) (hM : 0 < M) :
    familyWords (lfsrFamily K M) n = lfsrWords K M n := by
  ext x
  rw [mem_familyWords]
  constructor
  · rintro ⟨i, p, hp⟩
    rw [lfsrFamily_pref] at hp
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · have hp2 : p.2 = fun _ => (0 : K) := by
        funext j
        exact absurd j.isLt (by omega)
      have hzero : x = fun _ => (0 : K) := by
        rw [← hp, hp2]
        exact lfsr_pref_zero K p.1 n
      have hM' : NeZero M := ⟨by omega⟩
      rw [mem_lfsrWords]
      exact ⟨fun _ => 0, fun _ => 0, by rw [lfsr_pref_zero K, hzero]⟩
    · have : NeZero i.val := ⟨by omega⟩
      refine lfsrWords_monotone K n hi (by have := i.isLt; omega) ?_
      rw [mem_lfsrWords]
      exact ⟨p.1, p.2, hp⟩
  · intro hx
    rw [mem_lfsrWords] at hx
    obtain ⟨c, σ, hcσ⟩ := hx
    refine ⟨⟨M, by omega⟩, (c, σ), ?_⟩
    rw [lfsrFamily_pref]
    exact hcσ
