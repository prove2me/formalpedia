-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_witness_length_recurrence
-- name    : WitnessIsolation.AffineCollapse.witness_length_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:48.107274+00:00
-- url     : https://prove2.me/theorems/09ce3f7f-1fe9-45d3-a892-6c1c91d637c7
-- title:
--   Corollary 6.1 — Recurrence
-- statement:
--   Fix a polynomial-resource pruning transformation I. There exist integers A≥1 and B≥2, depending only on I and the encoding, such that for every guarantee p of I and every fixed ζ>0 there is a witness threshold v₀. For all v≥v₀, 2≤t≤v satisfying
--
--   $$p(tv)\ge\frac{2+\zeta}{t+1},$$
--
--   and every s≥v, one has
--
--   $$S(s,v)\le(s+2)^A[1+S((s+2)^B,t)].$$
--
--   The choices A,B precede ζ, p and all varying lengths; the threshold may depend on p, its guarantee threshold, and ζ. No monotonicity or computability of p is imposed. This is the full witness-length recurrence, including its additive one and the polynomial query-length argument.
--
--   Differences from the source:
--   - encoding: minimum finite circuit size S → minimum in extended naturals, with finite attainment separately asserted by Equation (2.2); reason: this avoids default values and agrees with the natural minimum whenever a finite decider exists, as it does for every finite cap
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Corollary 6.1, printed p. 12, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Corollary 6.1: A and B depend on I and the encoding, and precede ζ and the guarantee. -/
theorem witness_length_recurrence (I : PruningFamily) (hI : IsPruner I) :
    ∃ A B : ℕ, 1 ≤ A ∧ 2 ≤ B ∧
      ∀ p : ℕ → ℝ, HasGuarantee I p → ∀ ζ : ℝ, 0 < ζ →
      ∃ v₀ : ℕ, ∀ v : ℕ, v₀ ≤ v → ∀ t : ℕ, 2 ≤ t → t ≤ v →
        (2+ζ)/((t:ℝ)+1) ≤ p (t*v) → ∀ s : ℕ, v ≤ s →
          satComplexity s v ≤ ((s+2)^A : ℕ) * (1 + satComplexity ((s+2)^B) t) := by sorry

end WitnessIsolation.AffineCollapse
