-- Prove2me | solution 1 for EnergyAscent.residue_seal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:03.229885+00:00
-- url     : https://prove2.me/submissions/24e19626-d663-4ed3-981c-984766f8c259

-- Sol generated from Combinatorics/EnergyAscentResidueSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentResidueSeal
import Theorems.Thm_EnergyAscent_branchLetter_eq_one_iff
import Theorems.Thm_EnergyAscent_branchLetter_eq_two_iff

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


theorem fam_isPT (m : ℤ) : IsPT (fam m).1 (fam m).2.1 (fam m).2.2 := by
  unfold IsPT fam; simp only; ring

theorem fam_pos {m : ℤ} (hm : 2 ≤ m) :
    0 < (fam m).1 ∧ 0 < (fam m).2.1 ∧ 0 < (fam m).2.2 := by
  refine ⟨?_, by simp only [fam]; omega, ?_⟩ <;> · simp only [fam]; nlinarith

/-- For even `m` the family member is primitive: an explicit Bézout relation
`k·(2m) − (m² − 1) = 1` with `m = 2k`. -/
theorem fam_coprime {k : ℤ} : Int.gcd (fam (2 * k)).1 (fam (2 * k)).2.1 = 1 := by
  have h : IsCoprime ((fam (2 * k)).1) ((fam (2 * k)).2.1) := by
    refine ⟨-1, k, ?_⟩
    simp only [fam]
    ring
  exact Int.isCoprime_iff_gcd_eq_one.mp h

/-- Deep in the family the leg ratio is large, so the branch letter is `2`. -/
theorem fam_letter_two {m : ℤ} (hm : 4 ≤ m) : branchLetter (fam m).1 (fam m).2.1 = 2 := by
  have hpos : 0 < (fam m).1 := by simp only [fam]; nlinarith
  rw [branchLetter_eq_two_iff hpos]
  simp only [fam]
  nlinarith

/-- The root of the Berggren tree carries the middle letter. -/
theorem root_letter_one : branchLetter 3 4 = 1 := by
  rw [branchLetter_eq_one_iff]; omega






open EnergyAscent in
theorem solution(M : ℤ) (hM : 0 < M) :
    ∃ a b c a' b' c' : ℤ,
      (0 < a ∧ 0 < b ∧ 0 < c ∧ IsPT a b c ∧ Int.gcd a b = 1) ∧
      (0 < a' ∧ 0 < b' ∧ 0 < c' ∧ IsPT a' b' c' ∧ Int.gcd a' b' = 1) ∧
      (a ≡ a' [ZMOD M] ∧ b ≡ b' [ZMOD M] ∧ c ≡ c' [ZMOD M]) ∧
      branchLetter a b ≠ branchLetter a' b' := by
  set m : ℤ := 2 + 2 * M with hmdef
  have hm4 : 4 ≤ m := by omega
  obtain ⟨p1, p2, p3⟩ := fam_pos (show (2 : ℤ) ≤ m by omega)
  have hcop : Int.gcd (fam m).1 (fam m).2.1 = 1 := by
    have : m = 2 * (1 + M) := by omega
    rw [this]; exact fam_coprime
  refine ⟨3, 4, 5, (fam m).1, (fam m).2.1, (fam m).2.2,
    ⟨by norm_num, by norm_num, by norm_num, by unfold IsPT; norm_num, by decide⟩,
    ⟨p1, p2, p3, fam_isPT m, hcop⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `m² − 1 ≡ 3 (mod M)` since `m ≡ 2 (mod M)`
    have : M ∣ (fam m).1 - 3 := ⟨4 * M + 8, by simp only [fam, hmdef]; ring⟩
    exact (Int.modEq_iff_dvd.mpr (by simpa using this)).symm.symm
  · have : M ∣ (fam m).2.1 - 4 := ⟨4, by simp only [fam, hmdef]; ring⟩
    exact (Int.modEq_iff_dvd.mpr (by simpa using this)).symm.symm
  · have : M ∣ (fam m).2.2 - 5 := ⟨4 * M + 8, by simp only [fam, hmdef]; ring⟩
    exact (Int.modEq_iff_dvd.mpr (by simpa using this)).symm.symm
  · rw [root_letter_one, fam_letter_two hm4]
    decide
