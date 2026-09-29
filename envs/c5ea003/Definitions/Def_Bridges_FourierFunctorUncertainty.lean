-- Prove2me | Definitions.Def_Bridges_FourierFunctorUncertainty
-- name    : Bridges_FourierFunctorUncertainty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:14.075282+00:00
-- url     : https://prove2.me/theorems/c17af7f3-194d-48fe-b638-ba366fc8a96b
-- title:
--   Aether Catalog definitions — Bridges_FourierFunctorUncertainty
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FourierFunctorUncertainty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FourierFunctorUncertainty.lean by skeleton subtraction
import Mathlib

/-!
# Fourier as a functor, cycle 1: correct naturality domain and a genuine uncertainty principle

This file continues `Catalog/Bridges/FourierAsFunctor.lean`. That file established a
finite-coordinate categorical model of character duality and proved two *negative* results:

* the discrete Fourier matrices are **not** a natural endomorphism of the identity functor on a
  category whose arrows are all linear maps, and
* contravariant duality alone does **not** force any support uncertainty bound.

Both negative results are answered here positively, with substantive hypotheses.

## Main results

* `FourierUncertainty.dftNatIso` : the discrete Fourier transform on `ZMod N` **is** a natural
  isomorphism once the arrows are restricted to the multiplicative-unit automorphisms of
  `ZMod N`, i.e. between the pullback representation functor and its inverse twist, both viewed
  as functors `SingleObj (ZMod N)ˣ ⥤ ModuleCat ℂ`. This identifies the correct naturality domain.
* `FourierUncertainty.donoho_stark` : the Donoho–Stark uncertainty principle
  `N ≤ |supp Φ| * |supp (𝓕 Φ)|` for every nonzero `Φ : ZMod N → ℂ`. This is the substantive
  replacement for the disproved "contravariance implies uncertainty" claim.
* `FourierUncertainty.donoho_stark_sharp` : the bound is attained exactly, by delta functions.
* `FourierUncertainty.donoho_stark_am_gm` : the additive form `4 * N ≤ (|supp Φ| + |supp 𝓕Φ|)^2`.
* `FourierUncertainty.dualMap_comp` and `FourierUncertainty.doubleDualEmb_natural` : arrow-level
  functoriality of the character dual and naturality of the biduality evaluation map, together
  with `doubleDualEquiv_natural`, the natural-isomorphism form for finite abelian groups.
-/

open CategoryTheory Finset ZMod AddChar

namespace FourierUncertainty

/-! ## 1. The correct naturality domain for the discrete Fourier transform -/

section Naturality

variable {N : ℕ} [NeZero N]

/-- Pullback of a function on `ZMod N` along multiplication by a unit, as a linear equivalence. -/
noncomputable def unitPullback (u : (ZMod N)ˣ) : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ) where
  toFun Φ := fun j => Φ (u.val * j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun Φ := fun j => Φ (u⁻¹.val * j)
  left_inv Φ := by
    funext j
    simp [← mul_assoc]
  right_inv Φ := by
    funext j
    simp [← mul_assoc]











end Naturality

/-! ## 2. The Donoho–Stark uncertainty principle -/

section Uncertainty

variable {N : ℕ} [NeZero N]

open scoped Classical in
/-- The support of a function on `ZMod N`, as a finite set. -/
noncomputable def fsupport (Φ : ZMod N → ℂ) : Finset (ZMod N) :=
  Finset.univ.filter fun j => Φ j ≠ 0






/-- The delta function at `a`. -/
noncomputable def delta (a : ZMod N) : ZMod N → ℂ := fun j => if j = a then 1 else 0






end Uncertainty

/-! ## 3. Arrow-level biduality: functoriality and naturality of the evaluation map -/

section Biduality

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The character dual of a homomorphism: precomposition, bundled as a homomorphism of the
character groups. This is the contravariant `Hom(-, ℂ)` operation on arrows. -/
def dualMap (f : A →+ B) : AddChar B ℂ →+ AddChar A ℂ where
  toFun ψ := ψ.compAddMonoidHom f
  map_zero' := by ext a; simp
  map_add' ψ χ := by ext a; simp





section Finite

variable [Finite A] [Finite B]



end Finite

end Biduality



/-! ## 4. A prime refinement: Tao's `|supp Φ| + |supp 𝓕Φ| ≥ p + 1` for two-element supports

Donoho–Stark is sharp in general, but for prime modulus Tao's uncertainty principle gives the
strictly stronger additive bound `|supp Φ| + |supp 𝓕Φ| ≥ p + 1`. We prove this bound
unconditionally in the two-element-support case, where it is equivalent to the statement that a
nonzero two-term exponential sum vanishes at most once. -/

section PrimeRefinement

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {Φ : ZMod p → ℂ} {a b : ZMod p}






end PrimeRefinement


/-! ## 5. Primality is essential: a composite counterexample to the Tao bound

For `N = 4` the indicator function of the subgroup `{0, 2}` is a fixed point of the Fourier
transform up to scale: both it and its transform have support of size two. Hence the additive
bound `|supp Φ| + |supp 𝓕Φ| ≥ N + 1` **fails** for composite modulus, while Donoho–Stark
`|supp Φ| * |supp 𝓕Φ| ≥ N` holds with equality. So the extremals of the multiplicative bound are
not only delta functions: subgroup indicators are extremal too. -/

section CompositeCounterexample

open scoped Classical

/-- The indicator function of the subgroup `{0, 2} ⊆ ZMod 4`. -/
noncomputable def subgroupIndicator : ZMod 4 → ℂ := fun j => if j = 0 ∨ j = 2 then 1 else 0














end CompositeCounterexample

end FourierUncertainty


