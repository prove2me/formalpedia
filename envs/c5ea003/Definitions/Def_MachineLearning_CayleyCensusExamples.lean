-- Prove2me | Definitions.Def_MachineLearning_CayleyCensusExamples
-- name    : MachineLearning_CayleyCensusExamples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:37:38.912233+00:00
-- url     : https://prove2.me/theorems/dc7db5fb-c36e-4f63-a968-5b7c8943e770
-- title:
--   Aether Catalog definitions — MachineLearning_CayleyCensusExamples
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CayleyCensusExamples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CayleyCensusExamples.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusMoments

/-!
# Worked censuses on the dihedral group `D₃`, and the sharpness of the hypotheses

The general theory proved in `MachineLearning.CayleyCensusInvariance` and
`MachineLearning.CayleyCensusMoments` is exercised here on `DihedralGroup 3`
(the symmetric group on three letters) with three different connection sets.
The point of the file is twofold: to *instantiate* the abstract invariance
statements on explicit data, and to *delimit* them by finite counterexamples.

Census tables (rows indexed by `n`, columns by `r 0, r 1, r 2, sr 0, sr 1, sr 2`):

* `rotSet = {r 1, r 2}` (a full conjugacy class):
  `n = 0..5` gives
  `[1,0,0,0,0,0]`, `[0,1,1,0,0,0]`, `[2,1,1,0,0,0]`, `[2,3,3,0,0,0]`,
  `[6,5,5,0,0,0]`, `[10,11,11,0,0,0]`.
* `reflSet = {sr 0, sr 1, sr 2}` (the reflection class):
  `[1,0,0,0,0,0]`, `[0,0,0,1,1,1]`, `[3,3,3,0,0,0]`, `[0,0,0,9,9,9]`, …
* `mixSet = {r 1, r 2, sr 0}` (inversion closed, *not* conjugation closed):
  `[1,0,0,0,0,0]`, `[0,1,1,1,0,0]`, `[3,1,1,0,2,2]`, `[2,6,6,7,3,3]`,
  `[19,11,11,8,16,16]`, `[30,46,46,51,35,35]`.
  Exactly four distinct rows appear, matching the four orbits
  `{r 0}, {r 1, r 2}, {sr 0}, {sr 1, sr 2}` of `⟨inversion, Aut(G, S)⟩`.

## Main results

* `mix_census_r1_eq_r2`, `mix_census_sr1_eq_sr2` — orbit degeneracies predicted
  by the general theorems.
* `mix_card_census_le_four` — the quantitative orbit bound realised.
* `refl_isClassFunction` — a normal Cayley graph gives an honest class function.
* `walkCount_inv_fails_without_invClosed` — the inversion hypothesis is *not*
  removable: for `S = {r 1}` one has `walkCount S 1 (r 1) ≠ walkCount S 1 (r 1)⁻¹`.
* `return_dominance_fails_for_odd_length` — the evenness hypothesis in
  `walkCount_two_mul_le_walkCount_two_mul_one` is *not* removable: at length `3`
  the rotation census is strictly larger at `r 1` than at the identity.
-/

namespace CayleyCensus

open DihedralGroup

/-- The dihedral group of order `6`, i.e. the symmetric group on three points. -/
abbrev D3 := DihedralGroup 3

/-- The rotation class `{r, r²}`: a full conjugacy class of `D₃`. -/
def rotSet : Finset D3 := {r 1, r 2}

/-- The reflection class `{s, sr, sr²}`: the other nontrivial conjugacy class. -/
def reflSet : Finset D3 := {sr 0, sr 1, sr 2}

/-- An inversion-closed but *not* conjugation-closed connection set. -/
def mixSet : Finset D3 := {r 1, r 2, sr 0}

/-- A connection set that is not even inversion closed. -/
def dirSet : Finset D3 := {r 1}





/-! ### A normal Cayley graph: the census is a class function -/



/-! ### An inversion-closed, non-normal connection set -/






/-! ### Sharpness of the hypotheses -/




end CayleyCensus


