-- Prove2me | Definitions.Def_KServer_nonneg_chunk_system
-- name    : KServer_nonneg_chunk_system
-- status  : Definition
-- author  : @kwal0203
-- created : 2026-10-30T17:18:58.252236+00:00
-- url     : https://prove2.me/theorems/87791c8f-da93-4385-881f-a06ce8c4bc49
-- title:
--   Chunk systems with nonnegative outcome weights
-- statement:
--   A finite weighted chunk system with online escapes, using the existing request, filtration, adapted-size, terminal-request, offline-cost, and conditional online-cost requirements. The weights satisfy
--
--   $$P_\omega\ge0,\qquad \sum_\omega P_\omega=1.$$
--
--   The original chunk-system structure requires strict positivity at every listed outcome; this interface also permits zero-weight outcomes. Size windows, expected-total thresholds, escape prices, and chunk-count bounds are retained as parameters.
--
--   The conditional expected total at a history atom is the weighted sum of total size over that atom divided by its mass. The Doob-jump predicate requires the usual absolute one-step bound on outcomes with positive weight:
--
--   $$P_\omega>0\ \Longrightarrow\ |F_{h+1}(\omega)-F_h(\omega)|\le j.$$
--
--   This representation supports constructions on a fixed finite sample space containing impossible branches. Passing to the positive support is a separate theorem; this definition does not establish that conversion or any recursive lower-bound construction.
--
--   **Formalization Note** Real division is total, so the conditional-total expression is defined even on a zero-mass atom. The jump predicate imposes no condition at zero-weight outcomes.
-- source:
--   Finite-support bookkeeping for Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a and stopping rule (1), and Claim 13. This is an auxiliary formalization interface, not a verbatim additional result of the paper. It weakens only strict weight positivity in the existing platform chunk-system structure.

import Definitions.Def_KServer_chunk_cond

namespace KServer

structure NonnegChunkSystemB (X : Type*) [MetricSpace X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  /-- the finite sample space -/
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  /-- outcome weights -/
  P : Ω → ℝ
  /-- the number of chunks -/
  m : ℕ
  /-- the filtration: time-`i` knowledge, encoded as atoms -/
  hist : ℕ → Ω → ℕ
  /-- the chunks -/
  chunk : Ω → Fin m → List (Set X)
  /-- the sizes -/
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 ≤ P ω
  hPsum : ∑ ω, P ω = 1
  hm : mLo ≤ m
  hm0 : 0 < m
  href : ∀ i j : ℕ, i ≤ j → ∀ ω ω', hist j ω = hist j ω' → hist i ω = hist i ω'
  hadapt : ∀ (i : Fin m) (ω ω' : Ω), hist (i + 1) ω = hist (i + 1) ω' →
    chunk ω i = chunk ω' i
  hsmeas : ∀ (i : Fin m) (ω ω' : Ω), hist i ω = hist i ω' → size ω i = size ω' i
  hne : ∀ ω i, ∀ S ∈ chunk ω i, S.Nonempty
  hlast : ∀ ω, (((List.ofFn (chunk ω)).flatten).getLast?) = some {t}
  hopt : ∀ ω, evaderOfflineCost s ((List.ofFn (chunk ω)).flatten) ≤ dist s t
  hsize : ∀ ω i, cLo ≤ size ω i ∧ size ω i ≤ cHi
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (E : EvaderAlgorithm X) (bail : List (Set X) → Bool),
    size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀),
        P ω * E.bailCost bail (((List.ofFn (chunk ω)).take i).flatten) (chunk ω i) price
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)

attribute [instance] NonnegChunkSystemB.instFin NonnegChunkSystemB.instDec

namespace NonnegChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}

/-- Conditional expected total, also defined on zero-weight outcomes. -/
noncomputable def condTotal (D : NonnegChunkSystemB X s t cLo cHi total price mLo)
    (h : ℕ) (ω : D.Ω) : ℝ :=
  (∑ ω' ∈ Finset.univ.filter (fun ω' => D.hist h ω' = D.hist h ω),
    D.P ω' * ∑ i, D.size ω' i) /
  (∑ ω' ∈ Finset.univ.filter (fun ω' => D.hist h ω' = D.hist h ω), D.P ω')

/-- The jump bound is required on outcomes of positive probability. -/
def DoobJumpBound (D : NonnegChunkSystemB X s t cLo cHi total price mLo) (jb : ℝ) : Prop :=
  ∀ (h : ℕ) (ω : D.Ω), 0 < D.P ω →
    |D.condTotal (h + 1) ω - D.condTotal h ω| ≤ jb

end NonnegChunkSystemB
end KServer


