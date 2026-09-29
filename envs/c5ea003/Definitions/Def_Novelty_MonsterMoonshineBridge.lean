-- Prove2me | Definitions.Def_Novelty_MonsterMoonshineBridge
-- name    : Novelty_MonsterMoonshineBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:41.957868+00:00
-- url     : https://prove2.me/theorems/5d9552bb-7d63-4cfd-a230-777f74c2838f
-- title:
--   Aether Catalog definitions — Novelty_MonsterMoonshineBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MonsterMoonshineBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MonsterMoonshineBridge.lean by skeleton subtraction
import Mathlib

/-!
# A coefficientwise bridge from group characters to moonshine series

The proposed product of all McKay--Thompson series is not presently a theorem, and in its
literal form it has basic normalization problems (recorded in `FUTURE_DIRECTIONS.md`).  This
file instead proves a rigorous bridge fundamental to the interpretation of moonshine
coefficients.

A graded finite `G`-set `X n` has a fixed-point (permutation-character) series for every
`g : G`.  The coefficientwise average of these series is exactly the orbit-counting series.
Thus a family of character-like q-expansions determines an enumerative generating function.
This is Burnside's lemma lifted, simultaneously in every grade, to formal q-series represented
by their coefficient functions.
-/

namespace MonsterMoonshineBridge

/-- A formal q-series over `ℕ`, represented by its coefficient function. -/
abbrev NatQSeries := ℕ → ℕ

variable (G : Type*) [Group G]
variable (X : ℕ → Type*) [∀ n, MulAction G (X n)]

section FixedPoint

variable [∀ n (g : G), Fintype (MulAction.fixedBy (X n) g)]

/-- The permutation-character coefficient at grade `n`: the number of points fixed by `g`. -/
def fixedPointCoefficient (g : G) (n : ℕ) : ℕ :=
  Fintype.card (MulAction.fixedBy (X n) g)

/-- The fixed-point q-series attached to a group element. -/
def fixedPointSeries (g : G) : NatQSeries :=
  fun n => fixedPointCoefficient G X g n

section OrbitCounting

variable [Fintype G]
variable [∀ n, Fintype (MulAction.orbitRel.Quotient G (X n))]

/-- The coefficient counting `G`-orbits in the `n`th graded piece. -/
def orbitCoefficient (n : ℕ) : ℕ :=
  Fintype.card (MulAction.orbitRel.Quotient G (X n))

/-- The orbit-counting q-series of the graded action. -/
def orbitSeries : NatQSeries :=
  fun n => orbitCoefficient G X n




end OrbitCounting



end FixedPoint

end MonsterMoonshineBridge


