-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_HydraCalibration
-- name    : Geometry_PythagoreanHydra_HydraCalibration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T13:08:50.047508+00:00
-- url     : https://prove2.me/theorems/310abfc2-9281-4bea-bffa-e3d1af2cbe4c
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_HydraCalibration
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.HydraCalibration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/HydraCalibration.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth

/-!
# Calibration of the Pythagorean Hydra: the bound is attained, and descent is necessary

Two complementary results close the analysis of the game.

**Sharpness.**  `exists_maximal_battle` produces, for every hydra `H` of Pythagorean
heads, an actual battle of length exactly `Phi k (H.map bergDepth)`, the upper bound of
`battle_depth_bound`.  Specialised to one head at depth `d` this says the longest battle
has exactly `1 + k + ⋯ + k^d` moves (`single_head_maximal_battle`).  So the length
function of the Pythagorean Hydra is *exactly* the geometric sum — an elementary
function.  There is no room for a Kirby–Paris/Goodstein-style independence phenomenon:
the termination statement comes with a primitive recursive (indeed elementary) witness,
so it is provable by `Σ₁`-induction on the potential.

**Necessity of descent.**  The reason is precisely that inverse Berggren moves go
*down* the tree.  If the regrowth rule is relaxed so that a regrown head may have the
same level (`HydraStepLe`) — let alone a larger one, as happens if the hydra regrows the
Berggren *children* of the chopped head (`BergChopDown`) — then termination fails
outright: `hydraStepLe_has_infinite_play` and `berg_children_infinite_battle` exhibit
explicit infinite plays.  The Pythagorean Hydra therefore sits exactly on the boundary:
strict Berggren descent is both sufficient and necessary for Hercules to win.
-/

namespace PythHydra

/-! ### Sharpness: the maximal battle -/





/-! ### Necessity: relaxing the descent condition destroys termination -/

/-- The hydra game in which a regrown head may have the *same* level as the chopped one. -/
inductive HydraStepLe : Multiset ℕ → Multiset ℕ → Prop
  | chop (m : ℕ) (H R : Multiset ℕ) (hle : ∀ x ∈ R, x ≤ m) : HydraStepLe (m ::ₘ H) (R + H)



/-- The Pythagorean Hydra with the regrowth rule reversed: the regrown heads are the
Berggren *children* of the chopped head (forward Berggren moves, going away from the
root). -/
inductive BergChopDown : Multiset (ℤ × ℤ × ℤ) → Multiset (ℤ × ℤ × ℤ) → Prop
  | chop (t : ℤ × ℤ × ℤ) (H R : Multiset (ℤ × ℤ × ℤ))
      (hR : ∀ s ∈ R, ∃ u : BStep, s = applyStep u t) : BergChopDown (t ::ₘ H) (R + H)


end PythHydra

/-!
## Lab notes (experimental data, all produced by `#eval` on the definitions above)

Descent of a sample triple under `parent`:
`(117,44,125) → (45,28,53) → (5,12,13) → (3,4,5)`.

Berggren depths of the primitive triples with odd first leg and hypotenuse `≤ 100`:
`(3,4,5) ↦ 0`, `(5,12,13) ↦ 1`, `(15,8,17) ↦ 1`, `(21,20,29) ↦ 1`, `(7,24,25) ↦ 2`,
`(33,56,65) ↦ 2`, `(35,12,37) ↦ 2`, `(39,80,89) ↦ 2`, `(45,28,53) ↦ 2`, `(55,48,73) ↦ 2`,
`(65,72,97) ↦ 2`, `(77,36,85) ↦ 2`, `(9,40,41) ↦ 3`, `(63,16,65) ↦ 3`, `(11,60,61) ↦ 4`,
`(13,84,85) ↦ 5`.

Spines: hypotenuses along `Aⁿ` are `5, 13, 25, 41, 61, 85, 113, 145` (centred squares),
along `Bⁿ` they are `5, 29, 169, 985, 5741, 33461, 195025, 1136689` (Pell/NSW numbers,
`c_{n+2} = 6c_{n+1} − c_n`).  So depth is `Θ(√c)` on one spine and `Θ(log c)` on the other.

Maximal battle lengths `phi k d`:

| d | k=1 | k=2 | k=3 |
|---|-----|-----|-----|
| 0 | 1 | 1 | 1 |
| 1 | 2 | 3 | 4 |
| 2 | 3 | 7 | 13 |
| 3 | 4 | 15 | 40 |
| 4 | 5 | 31 | 121 |
| 5 | 6 | 63 | 364 |
| 6 | 7 | 127 | 1093 |

`phi 3 5 = 364` is the constant appearing in `root_battle_bound`.
-/


