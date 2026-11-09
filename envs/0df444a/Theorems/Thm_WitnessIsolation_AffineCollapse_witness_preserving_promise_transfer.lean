-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_witness_preserving_promise_transfer
-- name    : WitnessIsolation.AffineCollapse.witness_preserving_promise_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:51.186439+00:00
-- url     : https://prove2.me/theorems/6d42a6ee-15f3-49af-88dd-b7f54743ae1f
-- title:
--   Lemma 3.3 — Witness-preserving promise transfer
-- statement:
--   There is a fixed polynomial P₀ and a fixed polynomial resource multiplier R such that, for 1≤v≤s, any size-T circuit separating uniquely satisfiable from unsatisfiable descriptions of actual length at most ℓ=P₀(s+v+2), with at most v variables, implies
--
--   $$S(s,v)\le R(s+v+2)(T+1).$$
--
--   The separator may behave arbitrarily on descriptions having several solutions. The witness bound v is unchanged. The polynomials are chosen before s,v and the separator, so the resource bound is uniform. This transfers a promise separator to exact SAT without introducing new witness variables.
--
--   Differences from the source:
--   - encoding: P₀ and poly(s,v) with fixed polynomial bounds → uniform natural monomials c(s+v+2)^k and d(s+v+2)^e, and the extended-natural minimum S; reason: monomial domination preserves the full polynomial claim in the fixed padded encoding; no numerical coefficient is specified by the source
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Lemma 3.3, printed p. 8, PDF p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Lemma 3.3. Both polynomial bounds are independent of the separator. -/
theorem witness_preserving_promise_transfer :
    ∃ c k d e : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ ∀ s v : ℕ, 1 ≤ v → v ≤ s →
      ∀ C : Circuit (paddedWidth (c*(s+v+2)^k)) 1,
        SeparatesUnique (c*(s+v+2)^k) v C →
        satComplexity s v ≤ (d*(s+v+2)^e*(C.size+1) : ℕ) := by sorry

end WitnessIsolation.AffineCollapse
