-- Prove2me | solution 1 for ProofsInTheBook.Chapter16.not_borsukConjecture_1325
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T15:18:15.41977+00:00
-- url     : https://prove2.me/submissions/b6ae1f0f-4955-4589-ac28-ced369019a72

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter16


/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its Kahn-Kalai (1993) disproof in
dimension `1325`.  The later `d ≥ 298` bound is due to Hinrichs-Richter
(2003) and uses a different construction.

Formalization status: this file defines finite color-class bookkeeping, states
the corrected `BorsukConjecture d` for covers of a bounded set by subsets of
itself in `EuclideanSpace ℝ (Fin d)`, packages a counterexample as
`KahnKalaiCertificate d`, and formalizes enough of the
Frankl-Wilson/Kahn-Kalai pipeline to prove the unconditional `chapter16`
statement.  The local construction currently proves an explicit counterexample
in the book's Kahn-Kalai dimension `d = 1325`, using the fixed-layer `p = 13`
Frankl-Wilson bound, the unordered cut-vector realization, and its
codimension-one zero-sum hyperplane reduction.  The earlier pointed `p = 17`
construction remains available as scaffolding and gives `4624 ≤ d ≤ 6848`.
Mathlib has Euclidean metric spaces and finite-set tools, but not this
Frankl-Wilson/Kahn-Kalai pipeline as an available theorem.

TODO (future): formalize the Hinrichs-Richter (2003) construction to reach d ≥ 298; needs a separate 2-distance-set / strongly-regular-graph construction not in the book's proof.

Mathlib search status (2026-05-24): no Frankl-Wilson theorem, modular
intersection theorem, Ray-Chaudhuri-Wilson theorem, or oddtown/eventown theorem
was present under those names or nearby combinatorial names.  The local
additions below provide the reusable diagonal-functional linear independence
core, its mod-2 oddtown specialization, and the prime modular-intersection
form needed by the pointed Kahn-Kalai construction.
-/

namespace ProofsInTheBook.Chapter16




























































































































































































































































































































































































/--
A Kahn-Kalai certificate gives failure of Borsuk's conjecture in that dimension.
-/
theorem not_borsukConjecture_of_certificate {d : ℕ} (cert : KahnKalaiCertificate d) :
    ¬ BorsukConjecture d := fun h =>
  cert.no_partition (h cert.S cert.bounded cert.pos_diam)

























end ProofsInTheBook.Chapter16

open ProofsInTheBook.Chapter16

theorem solution : ¬ BorsukConjecture 1325 :=
  not_borsukConjecture_of_certificate kahnKalaiCertificate_1325
