-- Prove2me | solution 1 for PythHydra.berg_children_infinite_battle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:33:26.656981+00:00
-- url     : https://prove2.me/submissions/5d875e52-5180-4fb0-b698-a7f241f4c3ee

-- Sol generated from Geometry/PythagoreanHydra/HydraCalibration.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_HydraCalibration
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

open PythHydra

/-! ### Sharpness: the maximal battle -/





/-! ### Necessity: relaxing the descent condition destroys termination -/







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
open PythHydra in
theorem solution:
    ∃ f : ℕ → Multiset (ℤ × ℤ × ℤ), ∀ i, BergChopDown (f i) (f (i + 1)) := by
  refine ⟨fun i => {addr (List.replicate i BStep.B)}, fun i => ?_⟩
  show BergChopDown {addr (List.replicate i BStep.B)} {addr (List.replicate (i + 1) BStep.B)}
  have h1 : ({addr (List.replicate i BStep.B)} : Multiset (ℤ × ℤ × ℤ))
      = addr (List.replicate i BStep.B) ::ₘ 0 := rfl
  have h2 : ({addr (List.replicate (i + 1) BStep.B)} : Multiset (ℤ × ℤ × ℤ))
      = ({addr (List.replicate (i + 1) BStep.B)} : Multiset (ℤ × ℤ × ℤ)) + (0 : Multiset (ℤ × ℤ × ℤ)) := by
    simp
  rw [h1, h2]
  refine BergChopDown.chop _ 0 _ ?_
  intro s hs
  refine ⟨BStep.B, ?_⟩
  rw [Multiset.mem_singleton] at hs
  rw [hs, List.replicate_succ]
  rfl
