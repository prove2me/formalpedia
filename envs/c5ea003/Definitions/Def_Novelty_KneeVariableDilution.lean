-- Prove2me | Definitions.Def_Novelty_KneeVariableDilution
-- name    : Novelty_KneeVariableDilution
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:03.423269+00:00
-- url     : https://prove2.me/theorems/c09bbf72-eccf-492d-9a15-75aab65fc150
-- title:
--   Aether Catalog definitions — Novelty_KneeVariableDilution
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KneeVariableDilution`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KneeVariableDilution.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid

/-!
# Variable tokenisation, the dilution semigroup, and geometric budget grids (NET-72, round 2)

This file continues `Novelty.KneeDilutionGrid`.  There the tokenisation tax was
modelled by a *uniform* tokens-per-word ratio `r`, and the knee was shown to obey
the multiplicative sandwich `r * (K - 1) < K_split ≤ r * K`.  Real tokenizers are
not uniform: French words cost a variable number of tokens.  Here we

* replace the uniform split by a **variable dilution** `varSplit w p`, where word
  `i` is spelt with `w i ≥ 1` tokens, each carrying an equal share `p i / w i`
  of that word's attention mass;
* prove `variable_dilution_law`: the knee of the diluted profile is sandwiched by
  the *cumulative token counts* of the top words,
  `cum w (K - 1) < knee (varSplit w p) tau ≤ cum w K`, where `K` is the undiluted
  knee.  This is the exact form of the NET-72 mechanism hypothesis: the knee is
  predicted by **tokens-per-word measured on the top-`K` words**, not by any
  additive domain offset;
* derive the two-sided consequence `variable_dilution_between_extremes` in terms
  of the smallest and largest tokens-per-word ratio;
* show the dilution operators form a semigroup, `tokenSplit_comp`, so successive
  domain shifts compose *multiplicatively* (`knee_tokenSplit_comp_le`);
* prove `geometric_grid_brackets_knee`: a geometric budget grid `1, 2, 4, 8, …`
  always brackets the knee within a factor `2`, however large the multiplicative
  tokenisation tax is.  This is the design consequence of the NET-72 failure:
  arithmetic grids (`8, 16, 24, 32`) are the wrong instrument for a
  multiplicative law, geometric grids are the right one.
-/

namespace Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. The dilution semigroup -/



/-! ### 2. Variable tokenisation -/

/-- Cumulative token count of the first `m` words. -/
def cum (w : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ range m, w i




/-- The word that token `j` belongs to. -/
noncomputable def wordOf (w : ℕ → ℕ) (j : ℕ) : ℕ := sInf {m | j < cum w (m + 1)}


/-- **Variable token dilution.**  Word `i` is spelt with `w i` tokens, each
carrying the equal share `p i / w i` of that word's attention mass. -/
noncomputable def varSplit (w : ℕ → ℕ) (p : ℕ → ℝ) : ℕ → ℝ :=
  fun j => p (wordOf w j) / w (wordOf w j)









/-! ### 3. Geometric grids survive a multiplicative tax -/




/-! ### 4. Mixed domains -/



end Catalog.Novelty.KneeDilutionGrid


