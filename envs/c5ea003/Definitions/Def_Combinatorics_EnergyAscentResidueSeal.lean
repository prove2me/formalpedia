-- Prove2me | Definitions.Def_Combinatorics_EnergyAscentResidueSeal
-- name    : Combinatorics_EnergyAscentResidueSeal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:41:44.17746+00:00
-- url     : https://prove2.me/theorems/a5017ffb-66bd-49ef-88b6-06482aeab711
-- title:
--   Aether Catalog definitions — Combinatorics_EnergyAscentResidueSeal
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EnergyAscentResidueSeal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EnergyAscentResidueSeal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters

/-!
# Energy-Ascent II: the branch letter is sealed against residues

Companion to `Combinatorics.EnergyAscentBerggrenLetters`.  There we proved that
the first Berggren branch letter `b₁` of a primitive Pythagorean triple is an
*exact* function of the leg ratio (a positional statistic).  Here we prove the
complementary negative half of the ENERGY-ASCENT dichotomy, replicating in
closed form the empirical "residue seal" (`N mod 3^k` null, worst `z = +1.97`):

> **No congruence datum of any modulus carries any information about `b₁`.**

Formally, for every modulus `M ≥ 1` there are two primitive Pythagorean triples
that are componentwise congruent mod `M` yet have different branch letters
(`EnergyAscent.residue_seal`); consequently the branch letter is *not* a
function of the residues `(a mod M, b mod M, c mod M)`
(`EnergyAscent.branchLetter_not_residue_function`), and the failure is not a
small-number accident: the seal persists arbitrarily high up the tree
(`EnergyAscent.residue_seal_unbounded`).

Together with `EnergyAscent.branchLetter_ratio_invariant` this is the formal
version of the round-70 slogan: *the tree letters are sealed against residues,
open to position.*
-/

namespace EnergyAscent

/-- The one-parameter family `(m² − 1, 2m, m² + 1)` of Pythagorean triples,
which is primitive exactly when `m` is even.  For `m = 2` it is the root
`(3, 4, 5)`; for `m ≥ 4` it lies deep in the third ratio band. -/
def fam (m : ℤ) : ℤ × ℤ × ℤ := (m ^ 2 - 1, 2 * m, m ^ 2 + 1)










end EnergyAscent


