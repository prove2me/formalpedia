-- Prove2me | Definitions.Def_NumberTheory_MolienNecklaceCongruence
-- name    : NumberTheory_MolienNecklaceCongruence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:17.807616+00:00
-- url     : https://prove2.me/theorems/78b6be0b-7a0f-4dc2-af2d-df7898ce779b
-- title:
--   Aether Catalog definitions — NumberTheory_MolienNecklaceCongruence
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.MolienNecklaceCongruence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/MolienNecklaceCongruence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10

/-!
# The Molien/Burnside machinery as an arithmetic engine: necklace congruences

This file is the number-theoretic pay-off of the Molien/Burnside framework of
`Catalog.NumberTheory.MolienBurnsideD10`.  The bridge is the *cycle-index* identity

`|X^g| = k ^ (number of ⟨g⟩-orbits on Y)`   for `X = Coloring Y k = (Y → Fin k)`,

proved here as `D10.Coloring.fixCount_coloring`.  Feeding it into the Burnside divisibility
`|G| ∣ ∑_{g ∈ G} |X^g|` for the rotation action of `ℤ/n` on itself yields the classical
**necklace congruence**

`n ∣ ∑_{a ∈ ℤ/n} k ^ gcd(n, a)`,

and, specialising to a prime, **Fermat's little theorem** `k^p ≡ k (mod p)`.  Thus the
Molien invariant, which the Klein four-group example of the companion file shows to be a
*strictly coarser* invariant than the Burnside mark vector, is nevertheless strong enough
to carry genuine arithmetic content.
-/

namespace D10

open Finset MulAction

/-- The set of `k`-colourings of `Y`.  This is a type synonym for `Y → Fin k`, introduced so
that we may equip it with the *permutation* action of a group acting on `Y` (rather than the
pointwise action on the values). -/
def Coloring (Y : Type*) (k : ℕ) : Type _ := Y → Fin k

namespace Coloring

variable {G Y : Type*} [Group G] [MulAction G Y] {k : ℕ}

instance [Fintype Y] [DecidableEq Y] : Fintype (Coloring Y k) :=
  inferInstanceAs (Fintype (Y → Fin k))

instance [Fintype Y] [DecidableEq Y] : DecidableEq (Coloring Y k) :=
  inferInstanceAs (DecidableEq (Y → Fin k))

instance : SMul G (Coloring Y k) := ⟨fun g f => (fun y => f (g⁻¹ • y) : Y → Fin k)⟩

theorem smul_apply (g : G) (f : Coloring Y k) (y : Y) :
    (g • f : Coloring Y k) y = f (g⁻¹ • y) := rfl

instance : MulAction G (Coloring Y k) where
  one_smul f := by funext y; rw [smul_apply, inv_one, one_smul]
  mul_smul g h f := by
    funext y
    rw [smul_apply, smul_apply, smul_apply, mul_inv_rev, mul_smul]

theorem smul_eq_self_iff (g : G) (f : Coloring Y k) :
    g • f = f ↔ ∀ y : Y, f (g • y) = f y := by
  constructor
  · intro h y
    have hy := congrFun (a := g • y) h
    rw [smul_apply, inv_smul_smul] at hy
    exact hy.symm
  · intro h
    funext y
    rw [smul_apply]
    have hy := h (g⁻¹ • y)
    rw [smul_inv_smul] at hy
    exact hy.symm

/-- The colourings fixed by `g` are exactly the functions on the set of `⟨g⟩`-orbits. -/
def fixedEquivOrbitFun (g : G) :
    {f : Coloring Y k // g • f = f} ≃
      (Quotient (MulAction.orbitRel (Subgroup.zpowers g) Y) → Fin k) where
  toFun f := Quotient.lift (fun y => (f.1 : Y → Fin k) y) (by
    rintro a b ⟨s, hs⟩
    have hg : g ∈ MulAction.stabilizer G f.1 := f.2
    have hsb : (s : G) ∈ MulAction.stabilizer G f.1 := (Subgroup.zpowers_le.mpr hg) s.2
    have hval := (smul_eq_self_iff (s : G) f.1).mp hsb b
    simp only at hs
    rw [← hs]
    exact hval)
  invFun h := ⟨(fun y => h (Quotient.mk _ y) : Y → Fin k), by
    rw [smul_eq_self_iff]
    intro y
    exact congrArg h (Quotient.sound ⟨⟨g, Subgroup.mem_zpowers g⟩, rfl⟩)⟩
  left_inv f := by ext; rfl
  right_inv h := by funext q; induction q using Quotient.inductionOn; rfl



end Coloring

section Rotation

variable {n : ℕ} [NeZero n]

/-- The rotation group `ℤ/n`, written multiplicatively, acting on `ℤ/n` by translation. -/
abbrev Rot (n : ℕ) := Multiplicative (ZMod n)






end Rotation

section Fermat




end Fermat

end D10


