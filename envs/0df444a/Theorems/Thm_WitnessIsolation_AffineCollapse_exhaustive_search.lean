-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_exhaustive_search
-- name    : WitnessIsolation.AffineCollapse.exhaustive_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:59.178478+00:00
-- url     : https://prove2.me/theorems/c9593526-cfda-4ea7-9255-b4db1a623e65
-- title:
--   Equation (2.2) — Exhaustive search and finite attainment
-- statement:
--   For every finite description cap s and variable cap v there is an exact SAT circuit attaining the minimum S(s,v). In particular, with 1≤v≤s there are uniform natural constants c,k such that
--
--   $$S(s,v)\le2^v c(s+v+2)^k.$$
--
--   The constants precede both caps. Finite attainment makes the extended-natural minimum coincide with ordinary circuit complexity, including when an intermediate query cap falls outside the paper's main range. Malformed padded inputs and descriptions over either cap are rejected. This is the source's exhaustive-search fact, not an additional numbered milestone.
--
--   Differences from the source:
--   - generalization: S defined for 1≤v≤s, and exhaustive search supplies a finite upper bound there → finite attainment asserted for every natural s,v; the stated quantitative bound retains 1≤v≤s; reason: every predicate on the finite padded input cube has a finite Boolean circuit; the extra caps make the interface total without changing any source instance
--   - encoding: 2^v(s+v+2)^{O(1)} → 2^v c(s+v+2)^k for uniform existential c,k; reason: this expresses the source unspecified polynomial overhead and invents no gate constant
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), §2, printed p. 7, PDF p. 8, definition of S and Eq. (2.2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Equation (2.2); also asserts existence and attainment for every finite cap. -/
theorem exhaustive_search :
    (∀ s v : ℕ, ∃ C : Circuit (paddedWidth s) 1,
      DecidesSAT s v C ∧ satComplexity s v = (C.size : ℕ∞)) ∧
    ∃ c k : ℕ, ∀ s v : ℕ, 1 ≤ v → v ≤ s →
      satComplexity s v ≤ (2^v*c*(s+v+2)^k : ℕ) := by sorry

end WitnessIsolation.AffineCollapse
