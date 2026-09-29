-- Prove2me | Definitions.Def_Applications_ActionSpectrum_Bridge
-- name    : Applications_ActionSpectrum_Bridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T22:38:55.150305+00:00
-- url     : https://prove2.me/theorems/b63cfa89-5eca-4b90-8c7c-85f92ac4f50e
-- title:
--   Aether Catalog definitions — Applications_ActionSpectrum_Bridge
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ActionSpectrum.Bridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ActionSpectrum/Bridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic

/-!
# Bridging the computable spectrum with Mathlib's orbit machinery, and Burnside's lemma

The definition `SubsetSpectrum.spec` counts orbits by taking the image of the map
`s ↦ orb G s` on `Finset.powersetCard`.  This file certifies that it really is the number of
orbits of the induced `G`-action on the type of `r`-element subsets:

* `SubsetSpectrum.spec_eq_card_orbitQuotient` :
  `t_r = |(r-subsets)/G|` in Mathlib's `MulAction.orbitRel` sense;
* `SubsetSpectrum.spec_mul_card_eq_sum_fixed` : **Burnside's mass formula** for the spectrum,
  `t_r · |G| = ∑_{g ∈ G} #{ s : |s| = r, g·s = s }`.

Together with the sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` of the basic file this gives an
independent handle on the spectrum: for instance the identity element alone contributes
`C(n,r)` to the right-hand sum.
-/

open Finset

namespace SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]

variable (G X) in
/-- The type of `r`-element subsets of `X`, carrying the induced `G`-action. -/
abbrev Subsets (r : ℕ) := {s : Finset X // s.card = r}

variable (r : ℕ)

instance : SMul G (Subsets X r) := ⟨fun g s => ⟨act g s.1, by rw [act_card, s.2]⟩⟩


instance : MulAction G (Subsets X r) where
  one_smul s := Subtype.ext (by change act (1 : G) s.val = s.val; exact act_one s.val)
  mul_smul g h s := Subtype.ext (by change act (g * h) s.val = act g (act h s.val); exact act_mul g h s.val)

instance : DecidableEq (Subsets X r) := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

instance : DecidableRel (MulAction.orbitRel G (Subsets X r)).r := fun s t =>
  decidable_of_iff (∃ g : G, g • t = s) (by
    constructor
    · rintro ⟨g, hg⟩; exact ⟨g, hg⟩
    · rintro ⟨g, hg⟩; exact ⟨g, hg⟩)





end SubsetSpectrum


