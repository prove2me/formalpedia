-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
-- name    : Bridges_InfiniteCubicMatchingsCayley
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:32.682136+00:00
-- url     : https://prove2.me/theorems/bee56e1a-95da-4652-b762-cec0a8f84df2
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsCayley
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsCayley`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsCayley.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
/-
# Cayley graphs: infinite cubic Berge–Fulkerson graphs from finite quotients

A cubic Cayley graph `cayley S` of a group `Γ` (with `S` a three-element, inverse-closed
generating set of non-identity elements) is a covering of the Cayley graph of any quotient
`Γ →* Δ` on which the generators stay distinct and nontrivial (`isLocalIsoAt_cayley`).

Combining this with `BergeFulkerson.of_covering` gives a group-theoretic source of infinite
examples:

* `cayley_bergeFulkerson_of_quotient` — if the (possibly finite) quotient Cayley graph
  satisfies Berge–Fulkerson, so does the infinite one upstairs;
* `cayley_bergeFulkerson_of_finite_quotient` — assuming only the *finite* Berge–Fulkerson
  conjecture, every cubic Cayley graph of an infinite group with a suitable finite quotient
  satisfies Berge–Fulkerson;
* `ladderGroup_*` — a concrete instantiation with `Γ = ℤ × ℤ/2`, whose Cayley graph is the
  infinite ladder and whose finite quotients are the prisms.
-/

namespace Bridges.InfiniteCubicMatchings

universe u v

section Cayley

variable {Γ : Type u} [Group Γ] {Δ : Type v} [Group Δ]

/-- The Cayley graph of `Γ` with respect to an inverse-closed set `S` of non-identity
elements: `x` and `y` are adjacent when `x⁻¹ * y ∈ S`. -/
def cayley (S : Set Γ) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hS1 : (1 : Γ) ∉ S) : SimpleGraph Γ where
  Adj x y := x⁻¹ * y ∈ S
  symm := by
    intro x y h
    have : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact hSinv _ h
  loopless := ⟨by intro x hx; rw [inv_mul_cancel] at hx; exact hS1 hx⟩

variable (S : Set Γ) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hS1 : (1 : Γ) ∉ S)




/-- Right multiplication by an involution of the connection set is a perfect matching of the
Cayley graph. -/
def cayleyInvolutionMatching (b : Γ) (hb : b ∈ S) (hb2 : b * b = 1) :
    PerfectMatching (cayley S hSinv hS1) where
  partner x := x * b
  isAdj x := by
    show x⁻¹ * (x * b) ∈ S
    simpa [← mul_assoc] using hb
  invol x := by
    show x * b * b = x
    rw [mul_assoc, hb2, mul_one]







end Cayley

/-! ## A concrete infinite cubic Cayley graph: the ladder group `ℤ × ℤ/2` -/

/-- The group `ℤ × ℤ/2`, written multiplicatively so that it is a `Group`. -/
abbrev LadderGroup := Multiplicative (ℤ × ZMod 2)

/-- The three generators `(±1, 0)` and `(0, 1)` of the ladder group. -/
def ladderGens : Set LadderGroup :=
  {Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (-1, 0), Multiplicative.ofAdd (0, 1)}

theorem ladderGens_inv_closed : ∀ s ∈ ladderGens, s⁻¹ ∈ ladderGens := by
  rintro s (rfl | rfl | rfl)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr (by decide))

theorem ladderGens_one_notMem : (1 : LadderGroup) ∉ ladderGens := by
  simp only [ladderGens]
  decide

/-- The Cayley graph of `ℤ × ℤ/2` on `{(±1,0), (0,1)}`: the infinite ladder. -/
abbrev ladderCayley : SimpleGraph LadderGroup :=
  cayley ladderGens ladderGens_inv_closed ladderGens_one_notMem



/-! ## An infinite cubic Cayley graph on three involutions: the infinite dihedral group -/

open DihedralGroup

/-- Three distinct reflections of the infinite dihedral group `DihedralGroup 0`. -/
def dihGens : Set (DihedralGroup 0) := {sr 0, sr 1, sr 2}

theorem dihGens_inv_closed : ∀ s ∈ dihGens, s⁻¹ ∈ dihGens := by
  rintro s (rfl | rfl | rfl) <;> simp [dihGens, inv_sr]

theorem dihGens_one_notMem : (1 : DihedralGroup 0) ∉ dihGens := by
  have h : ∀ i : ZMod 0, (1 : DihedralGroup 0) ≠ sr i := by
    intro i hi
    simp only [one_def] at hi
    cases hi
  simp [dihGens, h]

/-- The Cayley graph of the infinite dihedral group on the three reflections
`sr 0, sr 1, sr 2`. -/
abbrev dihCayley : SimpleGraph (DihedralGroup 0) :=
  cayley dihGens dihGens_inv_closed dihGens_one_notMem







end Bridges.InfiniteCubicMatchings


