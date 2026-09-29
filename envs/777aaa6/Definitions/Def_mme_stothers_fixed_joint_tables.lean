-- Prove2me | Definitions.Def_mme_stothers_fixed_joint_tables
-- name    : mme_stothers_fixed_joint_tables
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T20:41:01.51649+00:00
-- url     : https://prove2.me/theorems/3f6fa90a-fe09-469d-8361-2c2ed157e5b6
-- title:
--   Joint tables and target completion degree for the fixed Stothers profile
-- statement:
--   For the exact Davie--Stothers fourth-power profile, this package defines the 45 ordered supported triples of nine grades, the joint histogram of any marginally regular address, the fixed target histogram induced by Table 1, and the exact target completion degree after one mode word is fixed. The latter is the product of the nine marginal factorials divided by the product of the 45 target-cell factorials. These are definition-only interfaces for the completion-star and Salem--Spencer hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Section 5, Equation (5.2), printed pp. 354--356 and 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Chapter 4.2.

import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-- The 45 ordered joint types in the support of the fourth-power grading. -/
abbrev FixedHashSupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

abbrev FixedHashJointMultiplicityTable := FixedHashSupportTriple → ℕ

def fixedHashSupportedTypeAt {m : ℕ}
    (a : FixedMarginalSupportedAddress m)
    (k : Fin (fixedOuterLength m)) : FixedHashSupportTriple :=
  ⟨fixedAddressType a.1 k, by
    simpa only [fixedAddressType] using a.2.1 k⟩

/-- The ordered 45-cell joint histogram of a marginally regular address. -/
def fixedHashJointTable {m : ℕ}
    (a : FixedMarginalSupportedAddress m) :
    FixedHashJointMultiplicityTable :=
  fun sigma ↦ Fintype.card
    {k : Fin (fixedOuterLength m) // fixedHashSupportedTypeAt a k = sigma}

/-- The exact fixed target histogram, restricted to the 45 supported cells. -/
def fixedHashTargetJointTable
    (m : ℕ) (sigma : FixedHashSupportTriple) : ℕ :=
  fixedJointMultiplicity m sigma.1

/-- Number of completions of one fixed mode word with the exact target joint table. -/
def fixedHashTargetStarDegree (m : ℕ) : ℕ :=
  (∏ j : Fin 9, (fixedMarginalCount m j).factorial) /
    ∏ sigma : FixedHashSupportTriple,
      (fixedHashTargetJointTable m sigma).factorial

end MME.StothersFourth


