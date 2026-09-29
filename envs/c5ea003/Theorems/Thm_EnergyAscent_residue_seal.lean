-- Prove2me | Theorems.Thm_EnergyAscent_residue_seal
-- name    : EnergyAscent.residue_seal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:17:37.83059+00:00
-- url     : https://prove2.me/theorems/94342470-c008-4d56-9e4b-dfc74597b0d3
-- title:
--   Residue seal.
-- statement:
--   **Residue seal.**  For every modulus `M ≥ 1` there exist two primitive
--   Pythagorean triples with positive entries which are componentwise congruent
--   modulo `M` but whose Berggren branch letters differ.
--
--   ```lean
--   theorem EnergyAscent.residue_seal(M : ℤ) (hM : 0 < M) :
--       ∃ a b c a' b' c' : ℤ,
--         (0 < a ∧ 0 < b ∧ 0 < c ∧ IsPT a b c ∧ Int.gcd a b = 1) ∧
--         (0 < a' ∧ 0 < b' ∧ 0 < c' ∧ IsPT a' b' c' ∧ Int.gcd a' b' = 1) ∧
--         (a ≡ a' [ZMOD M] ∧ b ≡ b' [ZMOD M] ∧ c ≡ c' [ZMOD M]) ∧
--         branchLetter a b ≠ branchLetter a' b' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentResidueSeal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentResidueSeal.lean#L61

-- Thm stub generated from Combinatorics/EnergyAscentResidueSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentResidueSeal

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

open EnergyAscent

theorem EnergyAscent.residue_seal(M : ℤ) (hM : 0 < M) :
    ∃ a b c a' b' c' : ℤ,
      (0 < a ∧ 0 < b ∧ 0 < c ∧ IsPT a b c ∧ Int.gcd a b = 1) ∧
      (0 < a' ∧ 0 < b' ∧ 0 < c' ∧ IsPT a' b' c' ∧ Int.gcd a' b' = 1) ∧
      (a ≡ a' [ZMOD M] ∧ b ≡ b' [ZMOD M] ∧ c ≡ c' [ZMOD M]) ∧
      branchLetter a b ≠ branchLetter a' b' := by sorry
