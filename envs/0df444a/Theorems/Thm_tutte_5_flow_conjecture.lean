-- Prove2me | Theorems.Thm_tutte_5_flow_conjecture
-- name    : tutte_5_flow_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:47:39.123592+00:00
-- url     : https://prove2.me/theorems/d9dbada8-5f92-4a0f-a2aa-c55b803687f7
-- statement:
--   Tutte's 5-flow conjecture (1954): Every bridgeless (2-edge-connected) graph has a nowhere-zero 5-flow. Jaeger proved every bridgeless graph has a nowhere-zero 8-flow; Seymour proved 6-flow. The 5-flow case remains open.
-- source:
--   https://en.wikipedia.org/wiki/Nowhere-zero_flow

import Mathlib

import Mathlib

-- Tutte's 5-flow conjecture: every bridgeless graph has a nowhere-zero 5-flow
-- A nowhere-zero 5-flow: orientation + nonzero values in ZMod 5 with flow conservation
theorem tutte_5_flow_conjecture (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbridgeless : ∀ e : G.edgeSet, (G.deleteEdges {e.val}).Connected) :
    ∃ (orient : G.edgeSet → Bool) (flow : G.edgeSet → ZMod 5),
      (∀ e, flow e ≠ 0) ∧
      ∀ v : V,
        ∑ e : G.edgeSet, (if orient e = true ∧ e.val.out.2 = v then flow e
          else if orient e = false ∧ e.val.out.1 = v then flow e else 0) =
        ∑ e : G.edgeSet, (if orient e = true ∧ e.val.out.1 = v then flow e
          else if orient e = false ∧ e.val.out.2 = v then flow e else 0) := by
  sorry
