-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_const_mul
-- name    : Catalog.Novelty.KneeDilutionGrid.prefixMass_const_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:10:47.592243+00:00
-- url     : https://prove2.me/theorems/9f55dd11-6814-4b8e-832d-be4cdc3f312b
-- title:
--   PrefixMass const mul
-- statement:
--   Formal statement of `Catalog.Novelty.KneeDilutionGrid.prefixMass_const_mul` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.prefixMass_const_mul(c : ℝ) (p : ℕ → ℝ) (k : ℕ) :
--       prefixMass (fun i => c * p i) k = c * prefixMass p k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeDilutionGrid.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeDilutionGrid.lean#L73

-- Thm stub generated from Novelty/KneeDilutionGrid.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid

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

open Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. Profiles, retained mass, and the knee -/

theorem Catalog.Novelty.KneeDilutionGrid.prefixMass_const_mul(c : ℝ) (p : ℕ → ℝ) (k : ℕ) :
    prefixMass (fun i => c * p i) k = c * prefixMass p k := by sorry
