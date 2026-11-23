-- Prove2me | Theorems.Thm_proposition_4_5_safe_of_visible
-- name    : proposition_4_5_safe_of_visible
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:53:55.157126+00:00
-- url     : https://prove2.me/theorems/6f791a19-f082-43eb-b44a-d776fa16402b
-- title:
--   Proposition 4.5: safety on a visible segment
-- statement:
--   Assume $s$ captures $R$, choose $q\in R$ with $\operatorname{dist}(s,q)=\operatorname{dist}(s,R)$, and let $P$ be an $R$-segment visible from $q$ via a $q$–$r$ path $Q$ whose weight is at most $D=d-2\varepsilon\delta_{\max}$. Then every vertex of $P$ is $\varepsilon$-safe for $s$. This is the metric part of Proposition 4.5.
-- source:
--   Chang et al., STOC 2027 submission #440, proof of Proposition 4.5 (printed p. 19, PDF p. 21), triangle inequalities immediately following the selection of Q.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open DistributedMWC440.UpperBound
noncomputable section

theorem proposition_4_5_safe_of_visible {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (S R : Finset V) (k d ε : ℝ) (δ : Shifts S) (s : S)
    (hcapture : Captures W S R k d δ s) (q : V) (hq : q ∈ R)
    (hqr : dist W s.val q = setDist W s.val R)
    {C : Cycle W} {a b : V} (P : W.graph.Walk a b)
    (hseg : IsSegment C R P)
    (hvis : Visible C q P (d-2*ε*deltaMax S k d))
    {v : V} (hv : v ∈ P.support) : Safe W S k d ε δ s v := by sorry
