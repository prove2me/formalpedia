-- Prove2me | Definitions.Def_Novelty_KneeDilutionGrid
-- name    : Novelty_KneeDilutionGrid
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:30:27.516788+00:00
-- url     : https://prove2.me/theorems/210080fe-377a-44fc-92a4-1fd5636d1fbc
-- title:
--   Aether Catalog definitions — Novelty_KneeDilutionGrid
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KneeDilutionGrid`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KneeDilutionGrid.lean by skeleton subtraction
import Mathlib

/-!
# The knee of an attention budget: grids, dilution, and the French anomaly (NET-72)

This file formalises the structural content of the NET-72 measurement
**THE-FRENCH-KNEE-EXCEEDS-THE-GRID**.

The empirical situation: a limited-memory (top-`k` key retention) sweep over the
budget grid `{…, 24}` at context 512 and `{…, 32}` at context 1024 found that on
French prose *no* grid point reached the retention bar (`0.9648` and `0.9680`
retained at the best grid point).  On English prose, code and mathematics the
knee had always been inside the grid, and the observed domain shifts were small
(`±4` keys — "one fine-step").  French broke the bracket.

We prove five things about the underlying mathematics, using an **attention
profile** `p : ℕ → ℝ` (the attention mass carried by the `i`-th most important
key, so `p` is nonnegative and antitone), its prefix mass `prefixMass p k`
(the mass retained by a budget of `k` keys), and the **knee**
`knee p tau = sInf {k | tau ≤ prefixMass p k}` (the least budget meeting the bar).

* `knee_exceeds_grid`, `knee_exceeds_grid_max`, `net72_french_knee_beyond_grid` —
  the honest reading of a failed sweep: if every grid point falls below the bar
  then the knee is *strictly larger than every grid point*.  A grid can only ever
  certify a **lower** bound on the knee.
* `grid_underdetermines_knee` — and that lower bound is all one gets: for every
  target `N` beyond the grid there is a profile with *exactly the same retention
  at every grid point*, and knee exactly `N`.  So "knee > 32" is not evidence for
  "knee = 36"; the size of the excess is invisible to the sweep.
* `dilution_law` — the tokenisation mechanism, exactly.  If a domain shift splits
  every semantic unit into `r` tokens of equal share (mass-preserving dilution
  `tokenSplit`), then the knee scales *multiplicatively*:
  `r * (knee p tau - 1) < knee (tokenSplit r p) tau ≤ r * knee p tau`.
  Both ends are attained (`dilution_upper_sharp`, `dilution_lower_sharp`), so the
  sandwich cannot be tightened.
* `no_additive_domain_shift_law` — the refutation of the "±4 fine-step" law:
  for **every** offset `d` there is a profile and a tokens-per-word ratio for
  which the knee jumps by more than `d`.  A multiplicative law admits no uniform
  additive bracket, which is precisely why French escaped the grid.
* `accuracy_knee_decoupling` — full-context accuracy and the knee are logically
  independent: two domains with the *same* accuracies can have the knee ordering
  in either direction ("code: easier and cheaper", "French: easier and dearer").

All constants are explicit; nothing is asymptotic.
-/

namespace Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. Profiles, retained mass, and the knee -/

/-- Mass retained by a budget of `k` keys: the sum of the `k` largest attention
weights, when `p` lists the weights in nonincreasing order. -/
def prefixMass (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, p i

/-- The **knee**: the least key budget whose retained mass meets the bar `tau`. -/
noncomputable def knee (p : ℕ → ℝ) (tau : ℝ) : ℕ := sInf {k | tau ≤ prefixMass p k}










/-! ### 2. A failed grid sweep bounds the knee only from below -/




/-! ### 3. Flat and two-level profiles (the calibration objects) -/

/-- Flat profile: unit mass on each of the first `n` keys. -/
def unif (n : ℕ) : ℕ → ℝ := fun i => if i < n then 1 else 0




/-- Scaled flat profile: mass `c` on each of the first `n` keys. -/
def scaled (c : ℝ) (n : ℕ) : ℕ → ℝ := fun i => c * unif n i






/-! ### 4. A grid reading determines nothing above the grid -/

/-- Two-level profile: height `1` on the first `g` keys, height `c` on keys
`g, …, N-1`, then zero. -/
def twoLevel (g N : ℕ) (c : ℝ) : ℕ → ℝ := fun i => unif g i + c * (unif N i - unif g i)






/-! ### 5. The tokenisation mechanism: mass-preserving dilution -/

/-- **Token dilution.**  Each semantic unit `i` is spelt with `r` tokens, each
carrying an equal share `p i / r` of the unit's attention mass.  This is the
hypothesised mechanism behind the French anomaly: the tokenizer spends more
tokens per French word, so each individual token contributes less. -/
noncomputable def tokenSplit (r : ℕ) (p : ℕ → ℝ) : ℕ → ℝ := fun j => p (j / r) / r










/-! ### 6. Sharpness of the dilution law -/




/-! ### 7. No additive domain-shift law -/


/-! ### 8. Accuracy and knee are logically independent -/

/-- A measured domain cell: full-context accuracy together with its attention
profile. -/
structure DomainCell where
  /-- full-context accuracy of the cell -/
  acc : ℝ
  /-- attention profile (weights in nonincreasing order) -/
  weight : ℕ → ℝ
  /-- attention weights are nonnegative -/
  nonneg : ∀ i, 0 ≤ weight i
  /-- attention weights are sorted -/
  anti : Antitone weight

/-- The knee of a domain cell at bar `tau`. -/
noncomputable def DomainCell.knee (D : DomainCell) (tau : ℝ) : ℕ :=
  Catalog.Novelty.KneeDilutionGrid.knee D.weight tau


end Catalog.Novelty.KneeDilutionGrid


