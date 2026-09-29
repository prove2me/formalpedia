-- Prove2me | Definitions.Def_Bridges_FiniteAbelianUncertainty
-- name    : Bridges_FiniteAbelianUncertainty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:52.161877+00:00
-- url     : https://prove2.me/theorems/2441dbf9-bb92-4a23-82ab-b586f7ac9b7a
-- title:
--   Aether Catalog definitions — Bridges_FiniteAbelianUncertainty
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FiniteAbelianUncertainty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FiniteAbelianUncertainty.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Donoho–Stark uncertainty for arbitrary finite abelian groups

`Catalog/Bridges/FourierFunctorUncertainty.lean` proved the Donoho–Stark uncertainty principle on
`ZMod N`, where the characters are explicit roots of unity. This file shows the argument is
structural rather than cyclic: it needs only that characters have modulus one and that the
character-sum inversion formula holds. We therefore obtain the uncertainty principle for an
arbitrary finite abelian group `G`, with the Fourier transform taking values on the Pontryagin
dual `AddChar G ℂ`.

## Main results

* `FiniteAbelianUncertainty.gdft_inversion` : the character-sum inversion formula
  `∑_ψ ψ b · 𝓖f(ψ) = |G| · f b`.
* `FiniteAbelianUncertainty.donoho_stark_finite_abelian` : for every nonzero `f : G → ℂ`,
  `|G| ≤ |supp f| * |supp 𝓖f|`, the support on the right being taken in the dual group.
* `FiniteAbelianUncertainty.donoho_stark_sharp_delta` : the bound is attained by delta functions,
  so it is sharp for every finite abelian group.
-/

open Finset AddChar

namespace FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The Fourier transform of a function on a finite abelian group, valued on the dual group. -/
noncomputable def gdft (f : G → ℂ) (psi : AddChar G ℂ) : ℂ := ∑ a, psi (-a) * f a

open scoped Classical in
/-- Support of a function on the group. -/
noncomputable def gsupport (f : G → ℂ) : Finset G := Finset.univ.filter fun a => f a ≠ 0

open scoped Classical in
/-- Support of a function on the dual group. -/
noncomputable def dsupport (F : AddChar G ℂ → ℂ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi => F psi ≠ 0







/-! ## Sharpness -/

open scoped Classical in
/-- The delta function at `a`. -/
noncomputable def gdelta (a : G) : G → ℂ := fun x => if x = a then 1 else 0





end FiniteAbelianUncertainty


