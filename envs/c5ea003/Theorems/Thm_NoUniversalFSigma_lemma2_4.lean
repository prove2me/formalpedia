-- Prove2me | Theorems.Thm_NoUniversalFSigma_lemma2_4
-- name    : NoUniversalFSigma.lemma2_4
-- status  : Proved
-- author  : @username
-- created : 2026-10-23T06:24:56.56444+00:00
-- url     : https://prove2.me/theorems/d7ae8e34-d4b7-4c0e-89d2-7ca60e2cc272
-- title:
--   Lemma 2.4 — Baire measurable maps are continuous on a comeager $G_\delta$ set
-- statement:
--   Let $X$ be a Polish space, let $Y$ be a second-countable topological space, and let $f:X\to Y$ be Baire measurable. Then there is a subset $C\subseteq X$ such that
--   $$C\text{ is }G_\delta,\qquad X\setminus C\text{ is meager},\qquad f|_C:C\to Y\text{ is continuous}.$$
--   Continuity uses the subspace topology on $C$. Empty spaces are permitted. This is a preparatory category result for working with Baire measurable reductions.
-- source:
--   Ruijun Wang, There is no universal F_sigma equivalence relation, arXiv:2610.31052v1 (22 October 2026), Lemma 2.4, Section 2.3, https://arxiv.org/html/2610.31052v1

import Definitions.Def_NoUniversalFSigma261031052

set_option autoImplicit false

universe u v

/-- Lemma 2.4 of arXiv:2610.31052v1. -/

theorem NoUniversalFSigma.lemma2_4
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : NoUniversalFSigma.IsBaireMeasurable f) :
    ∃ C : Set X, IsGδ C ∧ IsMeagre Cᶜ ∧ Continuous (fun x : C => f x) := by sorry
