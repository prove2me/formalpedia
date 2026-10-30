-- Prove2me | Theorems.Thm_KServer_finite_chunk_certificate_iff
-- name    : KServer.finite_chunk_certificate_iff
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T02:36:17.23655+00:00
-- url     : https://prove2.me/theorems/e881b063-1938-458e-bcca-a5bb23512a63
-- title:
--   Exact finite-horizon verification of chunk-system online cost bounds
-- statement:
--   Let X be a finite metric space with marked points s,t. Fix a size window [cₗ,cᵤ], a required expected total T, an escape price p, and a minimum chunk count m₀. The following existence statements are equivalent:
--
--   $$(\exists H,\ \mathrm{FiniteCertificate}_H)\quad\Longleftrightarrow\quad\mathrm{OnlineChunkSystem}.$$
--
--   A finite-horizon certificate records a common bound H on the length of every sampled complete request sequence and tests the conditional cost bounds against tables of positions and bailout decisions on histories of length at most H. The full model instead quantifies over online algorithms and escape rules on arbitrary finite histories. All request-feasibility, filtration, size-window, offline-cost, expected-total, and minimum-count constraints are retained.
--
--   The equivalence makes the online-adversary test family finite for every fixed horizon on a finite metric space. It does not assert an efficient search algorithm or the existence of a certificate for arbitrary parameters.
-- source:
--   Finite-support consequence of the universal online cost tests in Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4, Lemma 12 and Lemma 15, equation (6), printed pp. 14 and 19–21. An explicitly derived formalization lemma for the platform ChunkSystemB model and KServer_finite_chunk_certificates interface, not a verbatim theorem in the paper.

import Definitions.Def_KServer_finite_chunk_certificates
open KServer

theorem KServer.finite_chunk_certificate_iff {X : Type*} [MetricSpace X] [Finite X] {s t : X}
    {cLo cHi T p : ℝ} {mLo : ℕ} :
    (∃ C : FiniteChunkSystemB X s t cLo cHi T p mLo,
      ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ↔
    (∃ D : ChunkSystemB X s t cLo cHi T p mLo,
      ∀ ω₁ ω₂ : D.Ω, D.hist 0 ω₁ = D.hist 0 ω₂) := by sorry
