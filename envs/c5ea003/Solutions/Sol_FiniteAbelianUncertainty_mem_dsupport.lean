-- Prove2me | solution 1 for FiniteAbelianUncertainty.mem_dsupport
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:36:58.006734+00:00
-- url     : https://prove2.me/submissions/c3ffd573-bb58-4541-961d-5de7443d571b

-- Sol generated from Bridges/FiniteAbelianUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FiniteAbelianUncertainty
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

open FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]










/-! ## Sharpness -/







open FiniteAbelianUncertainty in
open scoped Classical in
omit [DecidableEq G] in
@[simp]
theorem solution{F : AddChar G ℂ → ℂ} {psi : AddChar G ℂ} :
    psi ∈ dsupport F ↔ F psi ≠ 0 := by simp [dsupport]
