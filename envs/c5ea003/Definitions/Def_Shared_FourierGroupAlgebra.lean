-- Prove2me | Definitions.Def_Shared_FourierGroupAlgebra
-- name    : Shared_FourierGroupAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:59:03.71319+00:00
-- url     : https://prove2.me/theorems/2186fc94-6e58-4d90-b0b0-0db13034b7da
-- title:
--   Aether Catalog definitions — Shared_FourierGroupAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module Shared.FourierGroupAlgebra, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/FourierGroupAlgebra.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
/-
# The Fourier transform as the Wedderburn decomposition of `ℂ[G]`

For a finite abelian group `G`, the convolution algebra `ℂ[G] = AddMonoidAlgebra ℂ G` is
isomorphic, as a `ℂ`-algebra, to the algebra of *all* functions on the Pontryagin dual
`AddChar G ℂ` with pointwise multiplication.  This is the complete Wedderburn/Artin
decomposition of the group algebra in the abelian case: `ℂ[G] ≅ ℂ^{|G|}`, with the isomorphism
given by evaluating at characters, i.e. by the Fourier transform.

Main results:

* `FourierFA.evalHom_apply` : the evaluation-at-characters algebra map is `a ↦ (ψ ↦ ∑ₓ a x ψ x)`.
* `FourierFA.evalHom_eq_dft` : it is the Fourier transform of this development, up to inverting
  the character.
* `FourierFA.fourierAlgEquiv` : the algebra isomorphism `ℂ[G] ≃ₐ[ℂ] (AddChar G ℂ → ℂ)`.
* `FourierFA.isReduced_addMonoidAlgebra` : consequently `ℂ[G]` has no nonzero nilpotents.
-/


open Finset ComplexConjugate

namespace FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `x ↦ (ψ ↦ ψ x)`, as a monoid homomorphism from `Multiplicative G` to the algebra of
functions on the dual group. -/
noncomputable def charMonoidHom : Multiplicative G →* (AddChar G ℂ → ℂ) where
  toFun := fun x => fun ψ => ψ (Multiplicative.toAdd x)
  map_one' := by funext ψ; simp
  map_mul' := by
    intro x y
    funext ψ
    simp [AddChar.map_add_eq_mul]

/-- Evaluation at characters, as a `ℂ`-algebra map out of the group algebra. -/
noncomputable def evalHom : AddMonoidAlgebra ℂ G →ₐ[ℂ] (AddChar G ℂ → ℂ) :=
  AddMonoidAlgebra.lift ℂ (AddChar G ℂ → ℂ) G charMonoidHom

omit [DecidableEq G] in
theorem evalHom_apply (a : AddMonoidAlgebra ℂ G) (ψ : AddChar G ℂ) :
    evalHom a ψ = ∑ x : G, a x * ψ x := by
  rw [evalHom, AddMonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro x; simp)]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun x _ => by simp [charMonoidHom]

omit [DecidableEq G] in
/-- Evaluation at characters is exactly the discrete Fourier transform, read at the inverse
character. -/
theorem evalHom_eq_dft (a : AddMonoidAlgebra ℂ G) (ψ : AddChar G ℂ) :
    evalHom a ψ = dft (⇑a) (-ψ) := by
  rw [evalHom_apply, dft]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : conj ((-ψ) x) = ψ x := by
    rw [AddChar.neg_apply', map_inv₀, ← AddChar.inv_apply_eq_conj ψ x, inv_inv]
  rw [h]
  ring


theorem dft_injective : Function.Injective (dft : (G → ℂ) → AddChar G ℂ → ℂ) := by
  intro f g h
  rw [← dft_inversion f, ← dft_inversion g, h]

theorem evalHom_bijective :
    Function.Bijective (evalHom : AddMonoidAlgebra ℂ G → (AddChar G ℂ → ℂ)) := by
  constructor
  · intro a b hab
    have h : dft (⇑a) = dft (⇑b) := by
      funext ψ
      have := congrFun hab (-ψ)
      rw [evalHom_eq_dft, evalHom_eq_dft, neg_neg] at this
      exact this
    exact Finsupp.ext (fun x => congrFun (dft_injective h) x)
  · intro F
    refine ⟨Finsupp.equivFunOnFinite.symm (idft (fun ψ => F (-ψ))), ?_⟩
    funext ψ
    have hcoe : ⇑(Finsupp.equivFunOnFinite.symm (idft (fun ψ => F (-ψ))))
        = idft (fun ψ => F (-ψ)) := rfl
    rw [evalHom_eq_dft, hcoe, idft_inversion (fun ψ => F (-ψ))]
    simp

/-- **Wedderburn decomposition of the complex group algebra of a finite abelian group**:
`ℂ[G]` is isomorphic, as a `ℂ`-algebra, to the algebra of functions on the dual group,
the isomorphism being the Fourier transform. -/
noncomputable def fourierAlgEquiv : AddMonoidAlgebra ℂ G ≃ₐ[ℂ] (AddChar G ℂ → ℂ) :=
  AlgEquiv.ofBijective evalHom evalHom_bijective



end FourierFA


