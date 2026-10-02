-- Prove2me | solution 1 for BookSixth.orthonormal_pair_maps_to_std_basis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T14:20:07.455252+00:00
-- url     : https://prove2.me/submissions/f3d68a15-3d32-430e-a7f4-ee2b4b738913

import Mathlib
import Definitions.Def_BookSixth
-- `⨯₃` is `scoped[Matrix] infixl:74 " ⨯₃ " => crossProduct`
-- (Mathlib/LinearAlgebra/CrossProduct.lean:64) and `⬝ᵥ` is `scoped[Matrix]`
-- (Mathlib/Data/Matrix/Mul.lean:72).  The target's preamble is only
-- `open scoped BigOperators`, so `Matrix` has to be opened here for either to parse.
open scoped BigOperators Matrix InnerProductSpace
open BookSixth Matrix

/-- **Step 1 of the bridge to `BookSixth.standardizing_time_maps_are_similarities`.**

An orthonormal pair of directions in `Space3 = Fin 3 → ℝ` is carried to `e_0, e_1` by one
inner-product-preserving linear map.  `Space3` carries the *sup* norm and has no
`InnerProductSpace` instance, so the orthonormal-basis construction runs in
`E := EuclideanSpace ℝ (Fin 3) = PiLp 2`, where the inner product is *definitionally* the
goal's `∑ i, x i * y i`.  The third direction is `v ⨯₃ u`: orthogonal to both `u` and `v`
(`dot_cross_self`, `dot_self_cross`) and of unit length by Lagrange's identity
(`cross_dot_cross`), so `(u, v, v ⨯₃ u)` is an orthonormal basis of `E`.

**Why the map is one composition.**  Ten earlier candidates built `A` by hand as a
`LinearMap` on `Fin 3 → ℝ` with function `fun x => ofLp 2 (b.repr (toLp 2 x))`, re-proving
additivity with `change` and `rfl`; every one failed on *alias opacity* rather than
algebra, because a `have` is opaque and `change`/`rwa` could not connect an abbreviation to
the term `repr_self` talks about.  Two published declarations remove that layer:
`PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) : E →L[ℝ] (Fin 3 → ℝ)` (the
`WithLp`/`Space3` bridge, whose apply and symm-apply are `rfl`), and
`LinearIsometryEquiv.toContinuousLinearEquiv` (`LinearIsometry.lean:603`), which builds the
`≃SL` that the `≃ₗᵢ` coerces to.  Since `≃SL` and `→L` are two notations for the same
structure `ContinuousLinearMap`, `b.repr` is already a map of the goal's type.

mathematical unit: an inner-product-preserving `A : Space3 →L[ℝ] Space3` with
`A u = ![1,0,0]` and `A v = ![0,1,0]`, which is the whole content of this target.

first remote check: the `hWU` block, showing `‖v ⨯₃ u‖² = 1` from `cross_dot_cross`; it is
the only step with no accepted precedent on this target.

helper / child boundary: the `w`-normalisation could be published as its own child if it
proves hard in isolation; the remaining value goals are one `rw` each and do not warrant
one.

split decision: keep it whole.  The two blocks are individually small and the target is a
single conjunction.  The previous 97-line version was not too large, it was too indirect.

first remote unit: the `hWU` rewrite chain, which is where a CE would most likely land. -/
theorem solution :
    ∀ u v : Space3, (∑ i, u i * u i) = 1 → (∑ i, v i * v i) = 1 → (∑ i, u i * v i) = 0 →
      ∃ A : Space3 →L[ℝ] Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        A u = ![1, 0, 0] ∧
        A v = ![0, 1, 0] := by
  intro u v hu hv huv
  -- `dot_cross_self (v w) : w ⬝ᵥ v ⨯₃ w = 0` (Mathlib/LinearAlgebra/CrossProduct.lean:94)
  -- and `dot_self_cross (v w) : v ⬝ᵥ v ⨯₃ w = 0` (:87), both stated with `⬝ᵥ`, which *is*
  -- `∑ i, x i * y i`.  Both are `@[simp]`, so `simpa` would normalise their own statement
  -- to `True` and discard the content; the rewrite is the correct route.  At `v := v,
  -- w := u` these are precisely the two perpendicularity statements needed:
  -- `u ⬝ᵥ (v ⨯₃ u) = 0` and `v ⬝ᵥ (v ⨯₃ u) = 0`.
  have hUW : (∑ i, u i * (v ⨯₃ u) i) = 0 := by
    have e := dot_cross_self v u
    rwa [dotProduct] at e
  have hVW : (∑ i, v i * (v ⨯₃ u) i) = 0 := by
    have e := dot_self_cross v u
    rwa [dotProduct] at e
  -- Lagrange's identity `u ⨯₃ v ⬝ᵥ w ⨯₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w`, at
  -- `u = v`, `v = u`, `w = v`, `x = u`, reads
  -- `(v ⨯₃ u) ⬝ᵥ (v ⨯₃ u) = v ⬝ᵥ v * u ⬝ᵥ u - v ⬝ᵥ u * u ⬝ᵥ v = 1 * 1 - 0 * 0`.
  -- The two mixed factors are the *plain* dot products `v ⬝ᵥ u` and `u ⬝ᵥ v`; the first is
  -- turned into the second by swapping the two factors of each summand and both are then
  -- killed by `huv`.  `Finset.sum_comm` would not do this -- it is the *double*-sum
  -- generalisation (`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`,
  -- Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:105) and has no occurrence in a
  -- single sum, which is what candidate 3372 reported.  What is needed is only a swap of
  -- the factors of each summand, which `simpa only [mul_comm]` does directly.
  have hWU : (∑ i, (v ⨯₃ u) i * (v ⨯₃ u) i) = 1 := by
    have h := cross_dot_cross v u v u
    unfold dotProduct at h
    rw [hu, hv, huv] at h
    have hvu : (∑ i, v i * u i) = 0 := by
      simpa only [mul_comm] using huv
    rw [hvu] at h
    norm_num at h
    simpa using h
  -- The six inner products in `E`.  On `E` the inner product is *definitionally* the
  -- `∑ i, x i * y i` sum, so each of these is the corresponding sum equation under
  -- `PiLp.inner_apply` and `Real.inner_apply`, both of which are `rfl`-simp.
  have hUU : ⟪WithLp.toLp 2 u, WithLp.toLp 2 u⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using hu
  have hVV : ⟪WithLp.toLp 2 v, WithLp.toLp 2 v⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using hv
  have hUV : ⟪WithLp.toLp 2 u, WithLp.toLp 2 v⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using huv
  have hWU' : ⟪WithLp.toLp 2 (v ⨯₃ u), WithLp.toLp 2 (v ⨯₃ u)⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using hWU
  have hUW' : ⟪WithLp.toLp 2 u, WithLp.toLp 2 (v ⨯₃ u)⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using hUW
  have hVW' : ⟪WithLp.toLp 2 v, WithLp.toLp 2 (v ⨯₃ u)⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]; simp only [Real.inner_apply, PiLp.toLp_apply]; simpa using hVW
  -- `(u, v, v ⨯₃ u)` is an orthonormal family in `E`.  `orthonormal_iff_ite` reduces this
  -- to nine inner products, `fin_cases` discharges the index arithmetic, and each goal
  -- is one of the six equations above.  This block is carried over unchanged from earlier
  -- candidates, whose remote elaboration reached it and so type-checked it; it is the one
  -- part of the file with positive remote evidence.
  have hOr : Orthonormal ℝ (fun i : Fin 3 => WithLp.toLp 2
      (if i = 0 then u else if i = 1 then v else v ⨯₃ u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, reduceIte] <;>
      simp_all [PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply,
        real_inner_self_eq_norm_sq, real_inner_comm] <;>
      aesop
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range
      (fun i : Fin 3 => WithLp.toLp 2 (if i = 0 then u else if i = 1 then v else v ⨯₃ u))) :=
    (hOr.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  -- `OrthonormalBasis.coe_mk hOr hspan` states
  -- `⇑(OrthonormalBasis.mk hOr hspan) = fun i => WithLp.toLp 2 (if i = 0 then u else
  -- if i = 1 then v else v ⨯₃ u)`.  Evaluating at `0` and at `1` and reducing the `if` gives
  -- the value of the basis at those two indices, in the direction `(mk …) i = WithLp.toLp
  -- 2 …` that `rwa [h0]` needs below.  At index `1` the `if` reduces only one level, since
  -- `1 = 0` is false, so `if_pos rfl` discharges the remaining `if 1 = 1`.
  have hcoe : ⇑(OrthonormalBasis.mk hOr hspan)
      = fun i : Fin 3 => WithLp.toLp 2 (if i = 0 then u else if i = 1 then v else v ⨯₃ u) :=
    OrthonormalBasis.coe_mk hOr hspan
  have h0 : (OrthonormalBasis.mk hOr hspan) (0 : Fin 3) = WithLp.toLp 2 u := by
    have h := congr_fun hcoe (0 : Fin 3)
    simpa only [Fin.isValue, reduceIte] using h
  have h1 : (OrthonormalBasis.mk hOr hspan) (1 : Fin 3) = WithLp.toLp 2 v := by
    have h := congr_fun hcoe (1 : Fin 3)
    simp only [Fin.isValue, reduceIte] at h
    simpa only [if_pos rfl] using h
  -- The witness.  `PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) : E →L[ℝ] Space3`
  -- is the `WithLp` bridge (its apply is `rfl`), and `b.repr` coerces to `E →L[ℝ] E`
  -- via `instCoeTCContinuousLinearMap`.  Composing gives a map `Space3 →L[ℝ] Space3`
  -- directly -- no `LinearMap`, no `change`, no re-proved linearity.
  --
  -- The composition order is `ofLp ∘ repr ∘ toLp`: the input `x : Space3` enters through
  -- the *symmetric* leg `toLp`, the isometry `repr` acts in `E`, and `ofLp` leaves.  With
  -- `∘L` (infixr:80, Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean:483)
  -- this is written `A0 ∘L b.repr ∘L A0.symm`.  The middle factor needs the explicit
  -- conversion `LinearIsometryEquiv.toContinuousLinearEquiv`
  -- (Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:603), applied to the `repr`
  -- *field*: `OrthonormalBasis` is a structure whose single field `repr` is the
  -- `LinearIsometryEquiv` (PiL2.lean:390-392), not a subtype of one, so the conversion
  -- must be written `b.repr.toContinuousLinearEquiv`.  The implicit coercion is not
  -- available either: `instCoeTCContinuousLinearMap` (:842) is a `CoeTC` from
  -- `LinearIsometryEquiv`, and a `CoeTC` does not fire against `∘L`'s explicit `→SL`
  -- parameter.  Candidate 3393 reported the bare ascription mismatch at this line, and
  -- candidate 3395 reported
  -- `Invalid field toContinuousLinearEquiv: ... it is not possible to project the field
  -- toContinuousLinearEquiv from an expression OrthonormalBasis.mk hOr hspan of type
  -- OrthonormalBasis (Fin 3) ℝ (WithLp 2 Space3)` for the missing projection; the two
  -- diagnostics together localise the term exactly.
  --
  -- The whole witness carries an explicit `show` type.  `ContinuousLinearMap.comp` (:478)
  -- leaves its codomain `M₃` as a metavariable in the `∘L` notation, and `refine
  -- ⟨w, …⟩` elaborates the witness *before* the expected type is propagated from the goal,
  -- so the composition could not be closed.  Candidate 3397 reported exactly that:
  -- `(PiLp.continuousLinearEquiv …).symm has type (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 … but is
  -- expected to have type Space3 →L[ℝ] ?m.2180`, i.e. the unresolved codomain.  Stating the
  -- type first makes the codomain `Space3` known, and it is also the goal's own type, so
  -- the two cannot disagree.  `Al` is a plain `have` whose *value* is a literal term, so
  -- the `simp only [Al]` below is an ordinary rewrite rather than a definitional unfold.
  -- The composition is written as two explicit `ContinuousLinearMap.comp` applications
  -- rather than with the `∘L` notation.  Candidates 3399 and 3401 both failed to *parse*
  -- here, identically, with
  -- `type expected, got (?m ∘SL ?m ∘SL ?m : ?m →L[?] ?m)` and
  -- `unexpected token ':'`, and parenthesising the `∘L` chain did not change the
  -- diagnostic.  The notation is `@ContinuousLinearMap.comp _ _ _ … RingHomCompTriple.ids`
  -- with fourteen implicit arguments, and the resulting term is too ambiguous for the
  -- parser to use as the type of a `have` before the expected type is known.  Naming the
  -- function directly removes the notation from the equation entirely and lets the same
  -- expected-type propagation work as for any other term.
  -- The type is the *plain* `Space3 →L[ℝ] Space3`, and the composition appears only in the
  -- value.  Candidates 3399, 3401 and 3402 all failed identically at this declaration with
  -- `type expected, got (?m ∘SL ?m ∘SL ?m : ?m →L[?] ?m)` and
  -- `unexpected token ':'; expected command`, and the common factor is that all three put
  -- a *composition* in the type ascription: first as `∘L` (3399), then parenthesised `∘L`
  -- (3401), then as `ContinuousLinearMap.comp` (3402).  The error text renders the term
  -- with the `∘SL` notation even when the source does not, which is why the three look
  -- alike; what fails is the ascription, not the notation.  Writing the goal's own type
  -- and letting the value elaborate against it removes the ascription entirely.
  -- The two legs are obtained as *concretely typed* declarations, so no metavariable
  -- survives into the composition.
  --
  -- `LinearIsometryEquiv.toLinearIsometry` (`LinearIsometry.lean:535`) has type
  -- `E →ₛₗᵢ[ℝ] E`, and `LinearIsometry.toContinuousLinearMap` (`:284`) has type
  -- `E →SL[σ₁₂] E₂ = E →L[ℝ] E`. Composing that with `toContinuousLinearEquiv` is
  -- unnecessary: `toLinearIsometry` is the same isometry, and its `toContinuousLinearMap`
  -- is already a map of exactly the intermediate type. So `E2` is a single fully applied
  -- declaration with no metavariable at all.
  --
  -- Candidates 3404 and 3406 both failed inside a *nested* `ContinuousLinearMap.comp`,
  -- reporting the codomain of the inner application as still open
  -- (`Space3 →SL[?m.2173] ?m.2179` and then `EuclideanSpace ℝ (Fin 3) →SL[?m.2146]
  -- ?m.2152`). Naming the inner leg did not help, because the `have` type ascription is
  -- checked after the application's arguments, not before them. Removing the inner
  -- composition removes the metavariable at its source.
  -- The composition is done at the `LinearMap` level and lifted once, rather than
  -- composing `ContinuousLinearMap`s directly.
  --
  -- Seven consecutive candidates (3399, 3401, 3402, 3404, 3406, 3408, 3411) each failed on
  -- this one declaration, each for a different elaboration reason: a composition in *type*
  -- position is not parsed (3399, 3401, 3402), and a composition in *term* position leaves
  -- an implicit parameter of `ContinuousLinearMap.comp` open at whichever argument is
  -- checked first (3404, 3406, 3408, 3411).  `comp` is
  -- `def comp (g : M₂ →SL M₃) (f : M₁ →SL M₂) : M₁ →SL M₃` with `M₁ M₂ M₃` implicit, so
  -- each application must be solved by unification in the elaborator's chosen order, and
  -- naming a leg does not fix the order.
  --
  -- `LinearMap.comp` has no such parameters: `∘ₗ` is the composition on a *fixed* pair of
  -- modules that comes from the `SemilinearMap` structure, so the result type is determined
  -- outright and there is nothing to solve.  `LinearMap.toContinuousLinearMap`
  -- (`Topology/Algebra/Module/FiniteDimension.lean:299`) then lifts the composite to
  -- `Space3 →L[ℝ] Space3`; it is an `Equiv` needing `FiniteDimensional ℝ (Fin 3 → ℝ)` and
  -- `T2Space (Fin 3 → ℝ)`, both discharged by instance search.  This is the idiom Mathlib
  -- itself uses at `Analysis/InnerProductSpace/TwoDim.lean:123-124`.
  --
  -- `Eb ∘ₗ E2` is `ofLp (repr (toLp x))`: `∘ₗ g f` is `g ∘ f`, so the bridge `Eb` is outer
  -- and the isometry `E2` is inner.
  let Eb : EuclideanSpace ℝ (Fin 3) →L[ℝ] (Fin 3 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  -- `Ei` is the *inner* leg `repr ∘ toLp : Space3 →L[ℝ] E`, not the isometry alone.  It is
  -- built as a `LinearMap` composite for the same reason `Al` is: the `toLp` leg has type
  -- `Space3 →L[ℝ] E` and the isometry has type `E →L[ℝ] E`, and `∘ₗ` fixes the composite's
  -- type outright.  Candidate 3412 reported
  -- `↑E2 has type EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) but is expected to
  -- have type Space3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)`, which is exactly this: `E2` alone is
  -- `E →ₗ E` and the inner leg of a `Space3 →ₗ Space3` composite must be `Space3 →ₗ E`.
  let Ei : Space3 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearMap.toContinuousLinearMap
      ((OrthonormalBasis.mk hOr hspan).repr.toLinearIsometry.toContinuousLinearMap.toLinearMap ∘ₗ
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toLinearMap)
  let Al : Space3 →L[ℝ] Space3 :=
    LinearMap.toContinuousLinearMap (Eb.toLinearMap ∘ₗ Ei.toLinearMap)
  refine ⟨Al, ?_, ?_, ?_⟩
  -- Inner-product preservation.  This is the strongest test of the composition: it must
  -- round-trip `toLp`/`ofLp` on *both* sides.  `ContinuousLinearMap.coe_comp'` rewrites
  -- `⇑(h ∘SL f) = h ∘ f` and, being `rfl` and `[simp]`, collapses the *whole* three-fold
  -- composition in one `simp` -- unlike `comp_apply`, which is stated for a single `∘SL`
  -- and would need to be invoked three times.  The `rfl` lemmas `PiLp.toLp_apply` and
  -- `PiLp.ofLp` finish the journey.
  ·
    intro x y
    simp only [Al, Ei, Eb, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, PiLp.coe_continuousLinearEquiv,
      PiLp.coe_symm_continuousLinearEquiv, LinearMap.coe_toContinuousLinearMap,
      ContinuousLinearEquiv.coe_toLinearEquiv]
    have h := (OrthonormalBasis.mk hOr hspan).repr.inner_map_map (WithLp.toLp 2 x)
      (WithLp.toLp 2 y)
    -- `inner_map_map` states the goal with `E`'s inner product; the goal is the plain
    -- `∑ i, x i * y i` form, and on both sides the two `WithLp` layers are
    -- `PiLp.toLp_apply` (`rfl`) and `WithLp.ofLp` (definitional).
    -- `WithLp.ofLp` is a *structure field* (`WithLp.lean:54`), so it takes the structure and
    -- not the exponent: `ofLp 2 e` is not a term.  The bridge's own coefficient equation
    -- `PiLp.coe_continuousLinearEquiv` (`PiLp.lean:1145`, `rfl`) is the supported way to
    -- see through it, and `PiLp.inner_apply` is the matching one on the inner-product side.
    simpa only [PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply] using h
  -- `A u = ![1, 0, 0]`.  `repr_self (0 : Fin 3)` reads
  -- `repr ((mk hOr hspan) 0) = EuclideanSpace.single 0 1`, which is the right-hand side
  -- *inside* `E`; `h0` rewrites the argument.  Both facts are folded into the *single*
  -- equation `e2 : ofLp 2 (repr (toLp 2 u)) = toLp 2 (Pi.single 0 1)` that the goal
  -- actually has, so the `rw [e2]` matches exactly.  What remains is pointwise arithmetic:
  -- `![1,0,0]` is `vecCons 1 (vecCons 0 (vecCons 0 vecEmpty))` whereas `Pi.single 0 1`
  -- is built from an `if`, so the two agree on each index but are not definitionally equal
  -- -- hence `PiLp.ofLp_single`, then `ext i` and `fin_cases i`.
  · show ((OrthonormalBasis.mk hOr hspan).repr (WithLp.toLp 2 u) : Fin 3 → ℝ)
        = ![1, 0, 0]
    -- The goal is now `ofLp 2 (repr (toLp 2 u)) = ![1,0,0]`: the two `simp`d bridge
    -- applications are `ofLp` and `toLp`, which are `rfl`
    -- (`PiLp.coe_continuousLinearEquiv` and `PiLp.coe_symm_continuousLinearEquiv`), and
    -- `repr` sits between them, which is why the witness is `A0 ∘L b ∘L A0.symm`.
    have e2 : ((OrthonormalBasis.mk hOr hspan).repr (WithLp.toLp 2 u) : Fin 3 → ℝ)
        = (Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ) := by
      have e := (OrthonormalBasis.mk hOr hspan).repr_self (0 : Fin 3)
      rw [h0] at e
      -- `repr_self` reads `repr (b 0) = EuclideanSpace.single 0 1`, and `EuclideanSpace.single
      -- 0 1` is `PiLp.single 2 0 1`.  `PiLp.ofLp_single` (`PiLp.lean:152`) is the `rfl`
      -- equation `ofLp (single p i a) = Pi.single i a` that turns the right-hand side into
      -- the `Pi.single` form.  The left-hand side needs the `WithLp → Fin 3 → ℝ` projection,
      -- which is exactly the coercion in `e2`'s statement, so `exact` applies up to it.
      exact congrArg (fun z : WithLp 2 (Fin 3 → ℝ) => (z : Fin 3 → ℝ)) e
    rw [e2]
    ext i
    fin_cases i <;> simp [PiLp.toLp_apply]
  -- `A v = ![0, 1, 0]`, identically with index `1`.
  · show ((OrthonormalBasis.mk hOr hspan).repr (WithLp.toLp 2 v) : Fin 3 → ℝ)
        = ![0, 1, 0]
    have e2 : ((OrthonormalBasis.mk hOr hspan).repr (WithLp.toLp 2 v) : Fin 3 → ℝ)
        = (Pi.single (1 : Fin 3) 1 : Fin 3 → ℝ) := by
      have e := (OrthonormalBasis.mk hOr hspan).repr_self (1 : Fin 3)
      rw [h1] at e
      exact congrArg (fun z : WithLp 2 (Fin 3 → ℝ) => (z : Fin 3 → ℝ)) e
    rw [e2]
    ext i
    fin_cases i <;> simp [PiLp.toLp_apply]
