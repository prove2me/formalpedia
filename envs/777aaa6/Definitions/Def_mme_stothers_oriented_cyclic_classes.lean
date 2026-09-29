-- Prove2me | Definitions.Def_mme_stothers_oriented_cyclic_classes
-- name    : mme_stothers_oriented_cyclic_classes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T21:32:25.170408+00:00
-- url     : https://prove2.me/theorems/d6e42a2a-ac0b-46be-ad58-7526132645e7
-- title:
--   The fifteen oriented cyclic orbits of the ten Stothers Table-1 classes
-- statement:
--   The ten symmetry classes in Davie--Stothers Table 1 split into fifteen cyclic orbits: the five classes with a three-element full permutation orbit contribute one cyclic orientation, and the five classes with six distinct permutations contribute both an orientation and its first-two-mode transpose. This definition records the class map, the transpose flag, and an ordered grade-triple representative for each of those fifteen cyclic orbits. It is independent of the Coppersmith--Winograd parameter and can be reused in exact fourth-power source decompositions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Table 1 and Section 5, pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_six_symmetrized_tau_value
import Mathlib.Data.Fin.VecNotation

namespace MME.StothersFourth

def fixedModeRelabel (e : Equiv.Perm (Fin 3))
    (ρ : Fin 3 → Fin 9) : Fin 3 → Fin 9 :=
  fun i ↦ ρ (e.symm i)

def fixedOrientedClass : Fin 15 → Fin 10 :=
  ![0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 7, 8, 9]

def fixedOrientedIsSwapped : Fin 15 → Bool :=
  ![false, false, true, false, true, false, true, false,
    false, false, true, false, true, false, false]

def fixedOrientedRep : Fin 15 → Fin 3 → Fin 9 :=
  ![classRep 0,
    classRep 1,
    fixedModeRelabel swapFirstTwoPerm (classRep 1),
    classRep 2,
    fixedModeRelabel swapFirstTwoPerm (classRep 2),
    classRep 3,
    fixedModeRelabel swapFirstTwoPerm (classRep 3),
    classRep 4,
    classRep 5,
    classRep 6,
    fixedModeRelabel swapFirstTwoPerm (classRep 6),
    classRep 7,
    fixedModeRelabel swapFirstTwoPerm (classRep 7),
    classRep 8,
    classRep 9]

end MME.StothersFourth


