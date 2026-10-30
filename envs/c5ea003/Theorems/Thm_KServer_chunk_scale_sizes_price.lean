-- Prove2me | Theorems.Thm_KServer_chunk_scale_sizes_price
-- name    : KServer.chunk_scale_sizes_price
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T02:12:05.563042+00:00
-- url     : https://prove2.me/theorems/2605fe3a-c7ba-4366-ac0e-9b5d04db9cc4
-- title:
--   Scaling chunk sizes and escape prices with an exact Doob-jump bound
-- statement:
--   Let C be a filtered chunk system with nonnegative sizes bounded above by c, required expected total T, escape price p, and minimum chunk count m. Suppose the Doob martingale of its total size has one-step absolute jumps bounded by j. For any real q satisfying 0 ≤ q ≤ 1, there is a chunk system C′ with parameters
--
--   $$c'=qc,\qquad T'=qT,\qquad p'=qp,$$
--
--   with the same actual chunk count and minimum count, whose expected total and Doob-jump bound satisfy
--
--   $$\mathbb E[\Sigma_{C'}]=q\,\mathbb E[\Sigma_C],\qquad |\Delta\mathbb E[\Sigma_{C'}\mid\mathcal F_h]|\le qj.$$
--
--   Constant initial information and nonempty chunks are preserved when they hold for C.
--
--   This is a homogeneity result for the certificate and escape parameters, while the underlying metric distances keep their original scale. It is useful when an adversarial construction provides mass and regularity estimates in relative form rather than at a prescribed normalization. Unlike preservation of an existing jump bound, the conclusion records its exact proportional improvement. The endpoint q=0 is included.
-- source:
--   Auxiliary lemma derived from the filtered chunk-system cost inequalities underlying Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, arXiv:2211.05753v2, Section 4, Lemma 12 and Lemma 15 (printed pp. 14 and 19–21), https://arxiv.org/html/2211.05753v2. Stated for the platform definitions KServer.ChunkSystemB, EvaderAlgorithm.bailCost, and ChunkSystemB.DoobJumpBound; the simultaneous scaling assertion is an explicitly derived formalization lemma, not a verbatim theorem of the paper.

import Definitions.Def_KServer_chunk_cond
open KServer

theorem KServer.chunk_scale_sizes_price {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∃ C' : ChunkSystemB X s t 0 (q * cB) (q * T) (q * pe) mL,
      C'.m = C.m ∧
      (∑ ω, C'.P ω * ∑ i, C'.size ω i) = q * (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
      ((∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) →
        ∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.DoobJumpBound (q * jb) := by sorry
