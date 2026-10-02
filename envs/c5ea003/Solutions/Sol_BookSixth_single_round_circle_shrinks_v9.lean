-- Prove2me | solution 1 for BookSixth.single_round_circle_shrinks_v9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T06:36:04.057977+00:00
-- url     : https://prove2.me/submissions/b5596379-bf59-4422-9720-99da4f079e79

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
open scoped BigOperators
open BookSixth

noncomputable section

--  The half-open parameter interval on which the shrinking similarity is a homeomorphism.

abbrev ShrinkParam := {t : ℝ // 0 ≤ t ∧ t < 1}

--  **Obligation 1: one round circle can be shrunk by a global similarity.**
--
-- This is the `n = 0` base case of
-- `BookSixth.perfect_circles_pairwise_unlinked_motion`
-- (`f6a7245e-187d-4a69-8b49-100cf7e4a1cc`): a family of ambient homeomorphisms whose images
-- stay round circles.
--
-- The motion is the global similarity `x ↦ (1 - t) • x + t • c`, where `c` is the circle's
-- centre.
--
-- **Why the parameter range is `[0, 1)`.** The scale `1 - t` vanishes at `t = 1`, where the
-- map collapses to the constant `c`. That is fatal not merely to being a homeomorphism but
-- to the *inverse* leg: the true inverse is `K t ⁻¹ y = (1 - t)⁻¹ • y - (t / (1 - t)) • c`,
-- whose second term blows up as `t → 1⁻`, so
-- the inverse cannot be jointly continuous in `(t, x)` across `t = 1` even on a
-- half-open domain containing `1`. An earlier draft of this file quantified over all
-- `t : ℝ` with both continuity legs stated on all of `ℝ × Space3`; that statement is false,
-- not merely unprovable. The claim below is therefore stated on the closed strip
-- `[0, 1) × Space3`, which is the correct domain for this motion.
--
-- **Why `K` is indexed by the subtype `{t // 0 ≤ t ∧ t < 1}` and not by all of `ℝ`.**
-- The parent statements `IsUnlink` and `perfect_circles_pairwise_unlinked_motion` fix
-- `K : ℝ → Space3 ≃ₜ Space3`, so a `ℝ`-indexed child cannot be spliced into them; but a
-- genuinely `ℝ`-total family agreeing with this similarity on `[0, 1)` does not exist
-- either. The forward leg `(1 - t) • x + t • c` tends to the *constant* `c` as `t → 1⁻`, so
-- joint continuity forces `K 1 = const c`, which is not a homeomorphism. Hence this child
-- delivers the shrinking motion on the open-ended half-interval where it actually exists,
-- and the *assembly* obligation — reaching the prescribed endpoint — remains with the
-- clearance and endpoint children, which is where it belongs.
--
-- **Why there is no clearance hypothesis.** The motion is a *global* similarity of all of
-- `Space3`, so it maps the whole configuration to a scaled copy and preserves disjointness
-- and unlinking automatically. A clearance contract is only needed by the different
-- operation that moves one circle while holding the rest fixed; see
-- `work/book_sixth_clearance_contract.md`. For this child the set of other components is
-- empty, so any such hypothesis would be vacuous.
--
-- **What this child does not deliver.** A single global similarity has one scale and one
-- translation, so it cannot send a general finite family to the fixed `standardCircle i`
-- in a prescribed order. The parent's endpoint obligation is therefore still open and is
-- not addressed here; this child establishes the base case for the *motion* obligations
-- only.
--
-- **v4.** Same mathematics as `single_round_circle_shrinks.lean`; only the presentation of
-- the zero-time anchor and the algebraic close of the inverse leg differ. `le_rfl` and
-- `zero_lt_one` replace the two `by norm_num` side conditions, and the inverse identity is
-- closed coordinatewise by a single `simp only` + `ring` instead of restating the target
-- as an intermediate `hdist` equality and then unfolding it in two further `change`s.

theorem solution (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ t0 : {t : ℝ // 0 ≤ t ∧ t < 1}, t0.1 = 0 → ∀ x, K t0 x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  have hrhopos : ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < 1 - t := by
    intro t ht0 ht1
    linarith
  -- The homeomorphism is a composition: scale by `1 - t`, then translate by `t • c`.
  -- `Homeomorph.smulOfNeZero` is a `protected def` at
  -- `Mathlib/Topology/Algebra/ConstMulAction.lean:353`, and `Homeomorph.vadd` is the
  -- `@[to_additive]` image of `Homeomorph.smul`, so it takes a single element of the
  -- ambient additive group, namely `t • c : Space3`. Composing them inherits both the
  -- inverse and the continuity proofs, so there is no `Equiv.ofBijective` and no
  -- `Classical.choose` to defend. Each component is bound to its type first: without
  -- that, `.trans` unification stalls on `ContinuousConstVAdd Space3 ?m`.
  -- The family is indexed by the subtype, so its parameter is a subtype value: `t.1` is
  -- the real number and `t.2` the pair of side conditions, whose own components are
  -- `t.2.1 : 0 ≤ t.1` and `t.2.2 : t.1 < 1`.
  let K : ShrinkParam → Space3 ≃ₜ Space3 :=
    fun t => (Homeomorph.smulOfNeZero (1 - t.1 : ℝ) (ne_of_gt (hrhopos t.1 t.2.1 t.2.2))
      ).trans (Homeomorph.vadd (t.1 • c : Space3))
  -- The two pointwise identities of the composite and its inverse. Both are stated once,
  -- at the top level, so the continuity legs, the identity case and the roundness case all
  -- reuse them instead of re-deriving the same expansion.
  have hKeq : ∀ t : ShrinkParam, ⇑(K t)
      = fun x : Space3 => (1 - t.1) • x + t.1 • c := by
    intro t
    funext x
    simp only [K]
    -- `rw` rather than `simp`: `simp` would also rewrite `t.1 • c` and close the goal
    -- with the wrong normal form, whereas these three rewrites expose exactly the
    -- composite, and the residue is then closed by commutativity of addition.
    rw [Homeomorph.trans_apply, Homeomorph.vadd_apply, Homeomorph.smulOfNeZero_apply]
    exact add_comm _ _
  have hKinv : ∀ t : ShrinkParam, ⇑(K t).symm
      = fun y : Space3 => (1 - t.1)⁻¹ • y - (t.1 / (1 - t.1)) • c := by
    intro t
    funext y
    simp only [K]
    rw [Homeomorph.symm_trans_apply, Homeomorph.vadd_symm_apply,
      Homeomorph.smulOfNeZero_symm_apply]
    show (1 - t.1)⁻¹ • (-(t.1 • c) +ᵥ y) = _
    -- The algebraic inverse of `y ↦ a • y + b`, with `a = 1 - t` and `b = t • c`, is
    -- `y ↦ a⁻¹ • y - a⁻¹ • b`, and here `a⁻¹ • b = (t / (1 - t)) • c`. Two earlier
    -- drafts of this file asserted the wrong constant -- one wrote `- c`, the other
    -- `c + (1 - t)⁻¹ • (y - t • c)` -- and each was refuted by an explicit discrepancy.
    funext i
    change (1 - t.1)⁻¹ • ((-(t.1 • c) +ᵥ y) i) = _
    change (1 - t.1)⁻¹ • (-(t.1 • c) i + y i) = _
    -- Unfolding `Pi.smul_apply` on the left and `Pi.sub_apply` on the right leaves a
    -- single scalar identity in one variable, which `ring` closes.
    simp only [Pi.smul_apply, Pi.sub_apply]
    ring
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · -- Forward leg, jointly continuous in `(t, x)`.
    rw [show (fun p : ShrinkParam × Space3 => (K p.1) p.2)
        = (fun p => (1 - p.1.1) • p.2 + p.1.1 • c)
        from funext fun p => congrFun (hKeq p.1) p.2]
    show Continuous (fun p : ShrinkParam × Space3 =>
      (1 - p.1.1) • p.2 + p.1.1 • c)
    fun_prop
  · -- Inverse leg, jointly continuous in `(t, x)`. The explicit inverse is
    -- `(1 - t)⁻¹ • y - (t / (1 - t)) • c`; well defined exactly because `0 < 1 - t`.
    rw [show (fun p : ShrinkParam × Space3 => (K p.1).symm p.2)
        = (fun p => (1 - p.1.1)⁻¹ • p.2 - (p.1.1 / (1 - p.1.1)) • c)
        from funext fun p => congrFun (hKinv p.1) p.2]
    show Continuous (fun p : ShrinkParam × Space3 =>
      (1 - p.1.1)⁻¹ • p.2 - (p.1.1 / (1 - p.1.1)) • c)
    -- `fun_prop` cannot use `Continuous.inv₀` here, because the nonvanishing of the
    -- scale is not an instance; it is supplied explicitly instead.
    have hne : ∀ p : ShrinkParam × Space3, (1 - p.1.1) ≠ 0 :=
      fun p => by
        exact ne_of_gt (by linarith [p.1.2.1, p.1.2.2])
    have hfst : Continuous (fun p : ShrinkParam × Space3 => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous (fun p : ShrinkParam × Space3 => p.2) := continuous_snd
    have hA : Continuous (fun p : ShrinkParam × Space3 => 1 - p.1.1) := continuous_const.sub hfst
    have hinv : Continuous (fun p : ShrinkParam × Space3 => (1 - p.1.1)⁻¹) :=
      continuous_iff_continuousAt.2 fun p => ContinuousAt.inv₀ (hA.continuousAt) (hne p)
    exact (hinv.smul hsnd).sub ((hfst.div hA hne).smul continuous_const)
  · intro t0 ht0 x
    -- `K t0` is the homothety of ratio `1 - t0 = 1` at time `t0 = 0`, i.e. the identity.
    have ht0' : t0 = (⟨0, le_rfl, zero_lt_one⟩ : ShrinkParam) := Subtype.ext ht0
    subst ht0'
    rw [show (((K (⟨0, le_rfl, zero_lt_one⟩ : ShrinkParam) : Space3 ≃ₜ Space3) : Space3 → Space3))
        = fun y : Space3 => (1 - (0 : ℝ)) • y + (0 : ℝ) • c
        from hKeq ⟨0, le_rfl, zero_lt_one⟩]
    simp
  · intro t
    -- Roundness is the accepted global-similarity lemma, applied once the composite map
    -- is in the exact form `a • x + b`. The rewrite is between *coerced* composites: the
    -- goal contains the eta-reduced `⇑(…)`, so rewriting a bare lambda would not match.
    rw [show ((K t : Space3 ≃ₜ Space3) : Space3 → Space3)
        = fun x : Space3 => (1 - t.1) • x + t.1 • c from hKeq t]
    -- `obtain` above destructs `hC` and therefore clears it, so the witness is
    -- re-supplied here in anonymous-constructor form. Passing `hC` itself is a hard
    -- `Unknown identifier` error at this point.
    exact BookSixth.similarity_preserves_roundness C (1 - t.1) (t.1 • c)
      (hrhopos t.1 t.2.1 t.2.2) ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩

end
