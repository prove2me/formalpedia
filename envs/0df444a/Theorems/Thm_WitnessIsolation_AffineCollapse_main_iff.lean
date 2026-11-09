-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_main_iff
-- name    : WitnessIsolation.AffineCollapse.main_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:56.933566+00:00
-- url     : https://prove2.me/theorems/3c609f6d-adea-49da-91e6-9b6804a5262c
-- title:
--   Theorem 1.1 — Main theorem
-- statement:
--   Fix arbitrary real numbers a>0 and C>0, and put
--
--   $$p_{a,C}(n)=2^{-C(\log_2\log_2(n+4))^a}.$$
--
--   Then a randomized, possibly nonuniform polynomial-resource pruning transformation with witness-length guarantee at least p_{a,C} exists if and only if
--
--   $$\mathrm{NP}\subseteq\mathrm{P/poly}.$$
--
--   The same transformation and one fixed polynomial resource bound act at every input length. A single eventual witness threshold works across every description length. Success is required on every nonempty affine solution set, without a supplied basis; output circuits are arbitrary. The pruning subset condition holds for every well-formed input and every tape, including outside the promise. The right side quantifies over every NP language, using genuine uniform polynomial-time Turing-machine verification, with independent nonuniform circuit families for their P/poly membership.
--
--   Both directions are the goal. Neither a fixed success exponent, a restriction on description length as a function of witness count, nor the recurrence in place of the language-class inclusion is substituted.
--
--   **Formalization Note** Existence of a guarantee at least this scale is expressed by using the scale itself as a lower bound. Hardwired advice is charged through the actual serialized implementing circuit. The reused Turing-machine definitions give uniform polynomial-time checking relations. The local NP membership predicate uses binary input strings and binary certificates with a uniform polynomial certificate bound.
--
--   Differences from the source:
--   - encoding: standard NP, P/poly and polynomial-resource pruning with success at least p≥p_{a,C} → binary-certificate NP through the published uniform Turing-machine checking relations, explicit bounded-fan-in circuit P/poly, and a pruning family whose guarantee lower bound is p_{a,C}; reason: these encode the same standard language classes and the same existential lower-bound assertion; advice is hardwired and charged, and no witness or affine data is an input
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Theorem 1.1, printed p. 2, PDF p. 3; Definition 2.1, printed pp. 6–7, PDF pp. 7–8; proof printed p. 12, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Theorem 1.1, both directions, for every positive real a and C. -/
theorem main_iff (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    (∃ I : PruningFamily, IsPruner I ∧ HasGuarantee I (isolationScale a C)) ↔ NPCollapse := by sorry

end WitnessIsolation.AffineCollapse
