-- Prove2me | Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce
-- name    : Couret_RecohCompactOrbitBridge_59017063a1ce
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:43.555986+00:00
-- url     : https://prove2.me/theorems/da2115c2-6dd3-4e52-afcf-36f41359be27
-- title:
--   Anchored two-torsion orbit checks
-- statement:
--   For an anchor $b_0\in B$, test the differences $u=c-b_0$ for $c\in C$ and accept when $2u=0$ and $C=B+u$. A right-fold deduplication discards a support if a later retained support passes this test. The anchor-membership hypothesis belongs to correctness theorems; the raw executable functions are defined for arbitrary anchors.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCompactOrbitBridge.lean; source file SHA-256 2210812918f698e754a80bfa765d762150858f96b474bf87485ecfd69522196f

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
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false

/-!
An anchored orbit test and a finite-list deduplication invariant.

The orbit test fixes one point of the left support and examines only the
points of the right support. It therefore examines three differences when
the right support has cardinal three. No ambient-group search is used.

The list routine retains the last representative of each orbit. This is a
deliberate model at the quotient level, not an assertion that its order or
chosen representatives equal the Python routine's first-retention order.
The results below concern represented orbits and pairwise inequivalence.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Fix one point in the left support; test differences to the right support. -/
def recohAnchoredOrbitCheck (b₀ : G) (B C : Finset G) : Bool :=
  decide (∃ c ∈ C, (c - b₀) + (c - b₀) = 0 ∧
    C = translateSupport B (c - b₀))





/-- The finite set of differences inspected by the anchored test. -/
def recohAnchoredDifferences (b₀ : G) (C : Finset G) : Finset G :=
  C.image (fun c => c - b₀)





/-- A right-fold implementation: omit a support when a later retained support
has the same two-torsion orbit. The supplied anchor is required to belong to
every input support in the correctness theorems. -/
def recohAnchoredOrbitDedup (anchor : Finset G → G) :
    List (Finset G) → List (Finset G)
  | [] => []
  | B :: rest =>
      let retained := recohAnchoredOrbitDedup anchor rest
      if retained.any (fun C => recohAnchoredOrbitCheck (anchor B) B C)
      then retained else B :: retained













section Finite

variable [Fintype G]

theorem recoh_torsion_orbit_eq_of_partner (B C : Finset G)
    (hBC : OrdinaryPartner B C) : torsionOrbit B = torsionOrbit C := by
  ext S
  simp only [mem_torsionOrbit]
  constructor
  · exact fun hBS => recoh_ordinary_partner_trans
      (recoh_ordinary_partner_symm hBC) hBS
  · exact recoh_ordinary_partner_trans hBC

/-- Two sound and complete representative families have exactly the same
finite family of two-torsion orbits. Their representative choices may differ. -/
theorem recoh_orbit_families_eq_of_sound_complete
    (R : G → ℕ) (P Q : Finset (Finset G))
    (hPsound : ∀ B ∈ P, B.card = 3 ∧ orderedSquare B = R)
    (hPcomplete : ∀ S : Finset G, S.card = 3 → orderedSquare S = R →
      ∃ B ∈ P, OrdinaryPartner B S)
    (hQsound : ∀ C ∈ Q, C.card = 3 ∧ orderedSquare C = R)
    (hQcomplete : ∀ S : Finset G, S.card = 3 → orderedSquare S = R →
      ∃ C ∈ Q, OrdinaryPartner C S) :
    P.image torsionOrbit = Q.image torsionOrbit := by
  apply Finset.Subset.antisymm
  · intro orbit horbit
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp horbit
    obtain ⟨hcard, hsquare⟩ := hPsound B hB
    obtain ⟨C, hC, hCB⟩ := hQcomplete B hcard hsquare
    exact Finset.mem_image.mpr
      ⟨C, hC, recoh_torsion_orbit_eq_of_partner C B hCB⟩
  · intro orbit horbit
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp horbit
    obtain ⟨hcard, hsquare⟩ := hQsound C hC
    obtain ⟨B, hB, hBC⟩ := hPcomplete C hcard hsquare
    exact Finset.mem_image.mpr
      ⟨B, hB, recoh_torsion_orbit_eq_of_partner B C hBC⟩

end Finite

end Couret.STROBO2TORS


