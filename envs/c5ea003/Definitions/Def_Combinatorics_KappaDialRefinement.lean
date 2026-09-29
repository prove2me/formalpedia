-- Prove2me | Definitions.Def_Combinatorics_KappaDialRefinement
-- name    : Combinatorics_KappaDialRefinement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:25.828806+00:00
-- url     : https://prove2.me/theorems/b7422827-c291-483c-84db-f0ebcc10a354
-- title:
--   Aether Catalog definitions — Combinatorics_KappaDialRefinement
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.KappaDialRefinement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/KappaDialRefinement.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_KappaRateDial
/-
# Refinements of the κ rate–dial: coprime-scale equidistribution, the valuation ladder,
# and the effective size of a cell sweep

Building on `Combinatorics.KappaRateDial`, this file pushes the "rate dial, not a position
dial" dichotomy in three directions.

1. **A coprime-statistic no-go theorem** (`cellCount_coprime_statistic`, and its
   equidistribution corollary `cellCount_coprime_residue`). The absence of a positional
   signal is not merely a statement about whole period blocks: for *any* modulus `M` coprime
   to the period `L` and *any* statistic `Q` depending only on `v mod M`, the divisibility
   cell and the event `Q` are *exactly independent* over one common period. In particular
   each residue class mod `M` receives exactly `κ(σ)` members of the cell inside `[0, L·M)`.
   A divisibility cell therefore carries *no* information about any coprime-measurable
   observable, uniformly.

2. **The valuation ladder** (`card_valPeriod_eq`). Refining "`p ∣ v`" to "`v_p(v) = e p`"
   produces, over the refined period `∏ p^{e p + 1}`, a cell of size *exactly* `∏ (p - 1)`,
   **independently of the exponents** `e`. Sharpening the resolution of the dial therefore
   changes only the period (the denominator), never the numerator: the rate dial is a pure
   geometric ladder `∏ p^{-e p} (1 - 1/p)`.

3. **Effective sweep size** (`sweep_image_card_le`, `sweepValues_card_eq_iff`). Because the
   prime `2` is a dead coordinate, a sweep over all `2^{|P|}` divisibility cells explores at
   most `2^{|P| - 1}` distinct rate values when `2 ∈ P`; and it attains that maximum exactly
   when the numbers `p - 1` over the odd primes of `P` have pairwise distinct subset
   products. Quantifying the effective number of degrees of freedom of a cell sweep is
   exactly what a max-statistic selection correction needs. The criterion is not vacuous:
   `sweep_collision_3_7_13` exhibits a prime set where it fails.

## Lab notes

`P = {2,3,5,7}`, `L = 210`, all-cleared cell, `M = 11`: each of the 11 residue classes mod
`11` inside `[0, 2310)` contains exactly `48` totatives of `210` — checked by the general
theorem and instantiated in `cellCount_coprime_residue_example`.

Valuation ladder for `p = 3`, `e = 0,1,2`: cells of size `2` inside periods `3, 9, 27`, i.e.
densities `2/3, 2/9, 2/27` — a clean geometric ladder with constant numerator.
-/


open Finset

namespace KappaDial


/-! ## 1. Equidistribution across residue classes at any coprime scale -/




/-! ## 2. The valuation ladder: exact `p`-adic valuation cells -/

/-- `InValCell P e v` says that `v` has `p`-adic valuation exactly `e p` for every `p ∈ P`. -/
def InValCell (P : Finset ℕ) (e : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ p ∈ P, p ^ (e p) ∣ v ∧ ¬ p ^ (e p + 1) ∣ v

instance (P : Finset ℕ) (e : ℕ → ℕ) : DecidablePred (InValCell P e) := by
  intro v; unfold InValCell; infer_instance

/-- The refined period `∏_{p ∈ P} p^{e p + 1}` of the valuation cell decomposition. -/
def valPeriod (P : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ p ∈ P, p ^ (e p + 1)







/-! ## 3. Effective size of a cell sweep -/

/-- The multiset of rate values explored by a full sweep over all `2^{|P|}` cells. -/
def sweepValues (P : Finset ℕ) : Finset ℕ :=
  P.powerset.image (fun T => kappaRaw P (fun p => decide (p ∈ T)))







/-! ## Worked instances -/

section Example





end Example

end KappaDial


