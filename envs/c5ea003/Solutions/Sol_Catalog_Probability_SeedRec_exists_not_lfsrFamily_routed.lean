-- Prove2me | solution 1 for Catalog.Probability.SeedRec.exists_not_lfsrFamily_routed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:15.953418+00:00
-- url     : https://prove2.me/submissions/ef715c2d-220f-46d8-b2c8-01c1c12ddfb9

-- Sol generated from Probability/PRNGRouterCapacity.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_PRNG_card_compressible_le
import Theorems.Thm_Catalog_Probability_SeedRec_PRNG_mem_compressible

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

omit [Fintype α] in
/-- **Router capacity ceiling.** A router over a finite family of generators can
reproduce at most `∑ i, |S i|` files of any given length: seed spaces add, and
nothing else is gained by being allowed to choose the generator. -/
theorem card_familyWords_le :
    (familyWords g n).card ≤ ∑ i, Fintype.card (S i) :=
  (Finset.card_biUnion_le).trans
    (Finset.sum_le_sum fun i _ => (g i).card_compressible_le n)


/-- **No free lunch for the seed-compression router.** As soon as the total
number of seeds is smaller than the number of files, some file is rejected by
*every* generator in the family. -/
theorem exists_not_family_routed
    (h : (∑ i, Fintype.card (S i)) < Fintype.card α ^ n) :
    ∃ x : Fin n → α, ∀ i, ¬ SeedCompressible (g i) n x := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin n → α)) ⊆ familyWords g n := by
    intro x _
    obtain ⟨i, hi⟩ := hc x
    exact (mem_familyWords g n).2 ⟨i, hi⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  exact absurd (hcard.trans (card_familyWords_le g n)) (by omega)





variable {S₀ S₁ : Type w} [Fintype S₀] [Fintype S₁]







variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K]










open Catalog.Probability.SeedRec in
theorem solution(M n : ℕ) (hK : 2 ≤ Fintype.card K)
    (hn : 2 * M + M + 2 ≤ n) :
    ∃ x : Fin n → K, ∀ i : Fin (M + 1), ¬ SeedCompressible ((lfsrFamily K M) i) n x := by
  set q := Fintype.card K with hq
  have hterm : ∀ i : Fin (M + 1), q ^ (2 * i.val) ≤ q ^ (2 * M) := by
    intro i
    exact Nat.pow_le_pow_right (by omega) (by have := i.isLt; omega)
  have hsum : (∑ i : Fin (M + 1), q ^ (2 * i.val)) ≤ (M + 1) * q ^ (2 * M) := by
    calc (∑ i : Fin (M + 1), q ^ (2 * i.val))
        ≤ ∑ _i : Fin (M + 1), q ^ (2 * M) := Finset.sum_le_sum fun i _ => hterm i
      _ = (M + 1) * q ^ (2 * M) := by simp [Finset.sum_const, mul_comm]
  have hMq : M + 1 ≤ q ^ M := by
    have : M + 1 ≤ 2 ^ M := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    exact this.trans (Nat.pow_le_pow_left hK M)
  have hstep : (M + 1) * q ^ (2 * M) ≤ q ^ M * q ^ (2 * M) :=
    Nat.mul_le_mul_right _ hMq
  have hcomb : q ^ M * q ^ (2 * M) = q ^ (2 * M + M) := by
    rw [← pow_add]; congr 1; omega
  have hlt : q ^ (2 * M + M) < q ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
  have hcap : (∑ i : Fin (M + 1), Fintype.card ((Fin i.val → K) × (Fin i.val → K)))
      < Fintype.card K ^ n := by
    have hcards : (∑ i : Fin (M + 1), Fintype.card ((Fin i.val → K) × (Fin i.val → K)))
        = ∑ i : Fin (M + 1), q ^ (2 * i.val) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Fintype.card_prod, two_mul, pow_add, hq]
    rw [hcards, ← hq]
    omega
  exact exists_not_family_routed (lfsrFamily K M) n hcap
