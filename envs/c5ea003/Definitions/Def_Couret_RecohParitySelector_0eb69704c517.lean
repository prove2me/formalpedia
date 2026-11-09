-- Prove2me | Definitions.Def_Couret_RecohParitySelector_0eb69704c517
-- name    : Couret_RecohParitySelector_0eb69704c517
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:13:34.533463+00:00
-- url     : https://prove2.me/theorems/f135ffd5-c624-478e-b9b8-a3fbd4eaeab1
-- title:
--   A ternary coordinate selected from parity representatives
-- statement:
--   Defines a deterministic optional primary-three coordinate: return none when the representatives lie in one translation orbit; otherwise scan the ordered coordinate list for the first passing ternary orbit check. Specializes this selector to the cyclic parity representatives generated from sparse square entries.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParitySelector.lean; source file SHA-256 c17657a92d6caa292995c99fb93b4623634d6b4d95a8fae5ba6263e804ec456a

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c

set_option autoImplicit false

/-!
Transport of the conditional ternary selector to the parity representatives.

A ternary observation is constant on each two-torsion orbit. Consequently
both the one-orbit predicate and every separating-coordinate predicate
depend only on the finite family of orbits. Scanning the same coordinate
order therefore returns exactly the same first coordinate, even when the
representatives or their deduplication order differ.

The definitions below concern typed mathematical inputs. They do not
identify Python list order, parsing, exceptions, or execution semantics.
-/

namespace Couret.STROBO2TORS

section FiniteFamilies

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Equality of orbit families supplies a partner in the other family. -/
theorem recoh_representative_transfer_of_orbit_families_eq
    (P Q : Finset (Finset G))
    (hPQ : P.image torsionOrbit = Q.image torsionOrbit)
    (B : Finset G) (hB : B ∈ P) :
    ∃ C ∈ Q, OrdinaryPartner C B := by
  have hm : torsionOrbit B ∈ Q.image torsionOrbit := by
    rw [← hPQ]
    exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
  obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hm
  refine ⟨C, hC, (mem_torsionOrbit C B).mp ?_⟩
  rw [hCB]
  exact (mem_torsionOrbit B B).mpr (recoh_ordinary_partner_refl B)

/-- Any observation constant on H-orbits has the same separation predicate
on two families representing the same quotient. -/
theorem recoh_orbit_separation_iff_of_orbit_families_eq
    {β : Type*} (observe : Finset G → β)
    (hconstant : ∀ B C, OrdinaryPartner B C → observe B = observe C)
    (P Q : Finset (Finset G))
    (hPQ : P.image torsionOrbit = Q.image torsionOrbit) :
    (∀ B ∈ P, ∀ C ∈ P, observe B = observe C → OrdinaryPartner B C) ↔
      ∀ B ∈ Q, ∀ C ∈ Q, observe B = observe C → OrdinaryPartner B C := by
  have transport : ∀ (A D : Finset (Finset G)),
      A.image torsionOrbit = D.image torsionOrbit →
      (∀ B ∈ A, ∀ C ∈ A, observe B = observe C → OrdinaryPartner B C) →
      ∀ B ∈ D, ∀ C ∈ D, observe B = observe C → OrdinaryPartner B C := by
    intro A D hAD hsep B hB C hC hread
    obtain ⟨B', hB', hB'B⟩ :=
      recoh_representative_transfer_of_orbit_families_eq D A hAD.symm B hB
    obtain ⟨C', hC', hC'C⟩ :=
      recoh_representative_transfer_of_orbit_families_eq D A hAD.symm C hC
    have hread' : observe B' = observe C' := by
      calc
        observe B' = observe B := hconstant B' B hB'B
        _ = observe C := hread
        _ = observe C' := (hconstant C' C hC'C).symm
    exact recoh_ordinary_partner_trans
      (recoh_ordinary_partner_trans (recoh_ordinary_partner_symm hB'B)
        (hsep B' hB' C' hC' hread')) hC'C
  exact ⟨transport P Q hPQ, transport Q P hPQ.symm⟩

/-- The bounded one-orbit checks agree when their orbit families agree. -/
theorem recoh_one_orbit_check_eq_of_orbit_families_eq
    (P Q : Finset (Finset G))
    (hP : ∀ B ∈ P, B.Nonempty) (hQ : ∀ B ∈ Q, B.Nonempty)
    (hPQ : P.image torsionOrbit = Q.image torsionOrbit) :
    recohOneOrbitCheck P = recohOneOrbitCheck Q := by
  apply Bool.eq_iff_iff.mpr
  rw [recoh_one_orbit_check_iff P hP, recoh_one_orbit_check_iff Q hQ]
  simpa using
    (recoh_orbit_separation_iff_of_orbit_families_eq (fun _ : Finset G => ())
      (fun _ _ _ => rfl) P Q hPQ)

end FiniteFamilies

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- A prospective ternary coordinate passes on exactly the same orbit
families, independently of the chosen representatives. -/
theorem recoh_ternary_orbit_check_eq_of_orbit_families_eq
    (P Q : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (hP : ∀ B ∈ P, B.Nonempty) (hQ : ∀ B ∈ Q, B.Nonempty)
    (hPQ : P.image torsionOrbit = Q.image torsionOrbit)
    (j : RecohPrimaryCoordinate q 3) :
    recohTernaryOrbitCheck q P j = recohTernaryOrbitCheck q Q j := by
  apply Bool.eq_iff_iff.mpr
  rw [recoh_ternary_orbit_check_iff q P hP j,
    recoh_ternary_orbit_check_iff q Q hQ j]
  exact recoh_orbit_separation_iff_of_orbit_families_eq
    (recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j))
    (recoh_cyclic_ternary_constant_on_ordinary q (recohCanonicalPrimaryData q 3) j)
    P Q hPQ

/-- The shared finite selector on an explicit representative family.
The coordinate order is the increasing presentation order used historically. -/
def recohTernaryChoiceFromRepresentatives
    (reps : Finset (Finset ((i : Fin d) → ZMod (q i)))) :
    Option (RecohPrimaryCoordinate q 3) :=
  if recohOneOrbitCheck reps then none
  else recohFirstPassing (recohTernaryOrbitCheck q reps) (Finset.univ.sort (· ≤ ·))

/-- Equality holds for the selected coordinate itself, not just for the
existence of a separating coordinate, because the scan orders are identical. -/
theorem recoh_ternary_choice_eq_of_orbit_families_eq
    (P Q : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (hP : ∀ B ∈ P, B.Nonempty) (hQ : ∀ B ∈ Q, B.Nonempty)
    (hPQ : P.image torsionOrbit = Q.image torsionOrbit) :
    recohTernaryChoiceFromRepresentatives q P =
      recohTernaryChoiceFromRepresentatives q Q := by
  have hone := recoh_one_orbit_check_eq_of_orbit_families_eq P Q hP hQ hPQ
  have htest : recohTernaryOrbitCheck q P = recohTernaryOrbitCheck q Q := by
    funext j
    exact recoh_ternary_orbit_check_eq_of_orbit_families_eq q P Q hP hQ hPQ j
  simp only [recohTernaryChoiceFromRepresentatives, hone, htest]

/-- The conditional selector actually scans the parity representative family. -/
def recohParityTernaryChoice
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Option (RecohPrimaryCoordinate q 3) :=
  recohTernaryChoiceFromRepresentatives q (recohCyclicParityRepresentatives q entries)

theorem recoh_cyclic_parity_representatives_nonempty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (B : Finset ((i : Fin d) → ZMod (q i)))
    (hB : B ∈ recohCyclicParityRepresentatives q entries) : B.Nonempty := by
  apply Finset.card_pos.mp
  rw [((recoh_cyclic_parity_representatives_cover q entries).1 B hB).1]
  decide





/-- Full equality with the historical first-coordinate selector on every
typed entry list, without a realizability or input-format assumption. -/
theorem recoh_parity_ternary_choice_eq_legacy
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    recohParityTernaryChoice q entries = recohSquareTernaryChoice q entries := by
  change recohTernaryChoiceFromRepresentatives q (recohCyclicParityRepresentatives q entries) =
    recohTernaryChoiceFromRepresentatives q (recohCyclicSquareRepresentatives q entries)
  exact recoh_ternary_choice_eq_of_orbit_families_eq q _ _
    (recoh_cyclic_parity_representatives_nonempty q entries)
    (recoh_cyclic_square_representatives_nonempty q entries)
    (recoh_cyclic_parity_orbit_families_eq_legacy q entries)













end Cyclic

end Couret.STROBO2TORS


