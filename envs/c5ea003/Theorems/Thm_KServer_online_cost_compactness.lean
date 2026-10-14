-- Prove2me | Theorems.Thm_KServer_online_cost_compactness
-- name    : KServer.online_cost_compactness
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:10:32.116895+00:00
-- url     : https://prove2.me/theorems/8d8602cc-ce53-4847-8b9e-a32e83d8f823
-- title:
--   Compactness of deterministic k-server cost bounds under finite testing
-- statement:
--   Fix a metric space $M$, a natural number $k$, an initial configuration $C_0$ of $k$ labeled servers, and any real-valued function $b$ on finite request sequences. Suppose every finite family $F$ of request sequences admits a deterministic online algorithm $A_F$, starting at $C_0$, with
--
--   $$
--   \operatorname{cost}_{A_F}(\sigma)\le b(\sigma)\qquad(\sigma\in F).
--   $$
--
--   Then there is a single deterministic online algorithm $A$, starting at $C_0$, such that
--
--   $$
--   \operatorname{cost}_A(\sigma)\le b(\sigma)\qquad\text{for every finite sequence }\sigma.
--   $$
--
--   Every algorithm in the statement satisfies the service constraint at all histories. No compactness, boundedness, or finiteness of the metric space is assumed. The conclusion has exactly the same cost bound, with no approximation loss.
--
--   This permits the construction of one global policy from compatible finite cost tests, without requiring the separate test policies themselves to agree. In particular, it applies to competitive bounds with one prescribed additive constant. The assertion covers all natural $k$, including degenerate cases; any existence required is supplied by the finite-family hypothesis.
-- source:
--   Original finite-testing compactness derivation for the mission model. Koutsoupias, The k-server problem (2009), Section 2, preprint pp. 6-7 (laziness), https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf; the existing proved platform theorem KServer.exists_lazy_algorithm (39afec83-2a07-413d-bfc0-5684a036fa7b); Mathlib c5ea003, Mathlib/Topology/Compactness/Compact.lean, CompactSpace.iInter_nonempty (https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Compactness/Compact.lean#L813). The present statement is a derived compactness lemma, not a numbered theorem quoted from the survey.

import Definitions.Def_KServer_model
open KServer

theorem KServer.online_cost_compactness (k : ℕ) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (b : List M → ℝ)
    (h : ∀ F : Finset (List M), ∃ A : OnlineAlgorithm k M,
      A.conf [] = C₀ ∧ ∀ σ ∈ F, A.cost σ ≤ b σ) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
      ∀ σ : List M, A.cost σ ≤ b σ := by sorry
