-- Prove2me | solution 1 for RepresentativeFunctions.finiteDimensional_transSpace_of_isRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:03.801682+00:00
-- url     : https://prove2.me/submissions/d99a32ab-001c-4707-bd72-e006f648faf7

-- Sol generated from Novelty/RepresentativeFunctions.lean
import Mathlib
import Definitions.Def_Novelty_RepresentativeFunctions
/-
# Representative functions on a free monoid and the Kleene–Schützenberger theorem

Following *Various bialgebras of representative functions on free monoids*, a function
`f : X* → K` is **representative** when its "coproduct" factors through a finite tensor:
`f(uv) = Σ_{i<n} g_i(u) h_i(v)`.  Its **graph** is the noncommutative series
`Σ_w f(w) w`, and the Kleene–Schützenberger theorem identifies representative functions
with the series admitting a **linear representation** `f(w) = λ μ(w) γ`, where
`μ : X* → M_n(K)` is a monoid morphism.

This file proves the full equivalence, in the form of a three-way cycle:

* `IsRepresentative f → FiniteDimensional K (transSpace f)`
  (`finiteDimensional_transSpace_of_isRepresentative`);
* `FiniteDimensional K (transSpace f) → HasLinearRep f`
  (`hasLinearRep_of_finiteDimensional`) — the Myhill–Nerode / Hankel-rank construction:
  the space spanned by the left translates of `f` is stable under the shift operators,
  and reading these operators in a basis produces the representation;
* `HasLinearRep f → IsRepresentative f` (`isRepresentative_of_hasLinearRep`).

The resulting `tfae` statement `representative_tfae` is the Kleene–Schützenberger
equivalence in the "representative function" formulation used by the paper.

We also prove the closure properties which make the representative functions a
subalgebra of `K^{X*}`: they are closed under scalar multiples, sums and the Hadamard
(pointwise) product, the latter through the tensor product of linear representations.
-/

open RepresentativeFunctions

variable {X K : Type*} [Field K]

/-! ## Translates -/




/-! ## Representative functions and linear representations -/







/-! ## Linear representation ⟹ representative -/


/-! ## Representative ⟹ finite dimensional Hankel space -/


/-! ## Finite dimensional Hankel space ⟹ linear representation -/


/-! ## The Kleene–Schützenberger equivalence -/


/-! ## The algebra of representative functions -/







open RepresentativeFunctions in
theorem solution{f : List X → K}
    (hf : IsRepresentative f) : FiniteDimensional K (transSpace f) := by
  obtain ⟨n, g, h, hgh⟩ := hf
  have hle : transSpace f ≤ Submodule.span K (Set.range h) := by
    rw [transSpace, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    have : ltrans w f = ∑ i, g i w • h i := by
      funext v
      simp only [ltrans, hgh w v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [SetLike.mem_coe, show (fun w => ltrans w f) w = ltrans w f from rfl, this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have : FiniteDimensional K (Submodule.span K (Set.range h)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range h)
  exact Submodule.finiteDimensional_of_le hle
