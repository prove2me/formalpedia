-- Prove2me | solution 1 for KnasterTarskiBridge.knaster_tarski
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:40.20605+00:00
-- url     : https://prove2.me/submissions/8a7eb50b-a2c5-4d5b-88df-e9d5bf7b65d5

-- Sol generated from Bridges/KnasterTarskiBridge.lean
import Mathlib
import Definitions.Def_Bridges_KnasterTarskiBridge

/-! # Knaster-Tarski Fixed Point Bridge

Proves the Knaster-Tarski theorem: every monotone function on a complete
lattice has a least fixed point (and greatest fixed point).

Complementary to Banach's metric-space fixed point theorem:

1. Banach: contraction on COMPLETE METRIC spaces → unique fixed point
2. Knaster-Tarski: monotone on COMPLETE LATTICES → least/greatest fixed points

The least fixed point is constructive: it's the infimum of all pre-fixed
points {x | f(x) ≤ x}.

Key proof insight: f(inf S) ≤ inf S because for any b ∈ S,
f(b) ≤ b and by monotonicity f(inf S) ≤ f(b) ≤ b. Conversely,
inf S ≤ f(inf S) because f(inf S) IS in S (by monotonicity:
f(inf S) ≤ inf S implies f(f(inf S)) ≤ f(inf S)).
-/

open KnasterTarskiBridge

universe u

variable {α : Type u} [CompleteLattice α]

/-! ## Section 1: Pre-fixed and Post-fixed Points -/




/-! ## Section 2: Knaster-Tarski Theorem (Least Fixed Point) -/

/-- Key lemma: f(inf of pre-fixed points) ≤ inf of pre-fixed points.
    For any pre-fixed point b, inf S ≤ b, so f(inf S) ≤ f(b) ≤ b. -/
theorem sInf_prefixed_le (f : α → α) (hf : Monotone f) :
    f (sInf (preFixed f)) ≤ sInf (preFixed f) := by
  rw [le_sInf_iff]
  intro b hb
  calc f (sInf (preFixed f)) ≤ f b := hf (sInf_le hb)
  _ ≤ b := hb

/-- Conversely: inf of pre-fixed points ≤ f(inf of pre-fixed points).
    From f(inf) ≤ inf, by monotonicity f(f(inf)) ≤ f(inf),
    so f(inf) is itself a pre-fixed point, hence inf ≤ f(inf). -/
theorem sInf_le_sInf_prefixed (f : α → α) (hf : Monotone f) :
    sInf (preFixed f) ≤ f (sInf (preFixed f)) := by
  have h := sInf_prefixed_le f hf
  exact sInf_le (hf h)


/-! ## Section 3: Least Fixed Point Properties -/



/-! ## Section 4: Dual Results (Greatest Fixed Point) -/






/-! ## Section 5: LFP ≤ GFP -/



open KnasterTarskiBridge in
theorem solution(f : α → α) (hf : Monotone f) :
    f (sInf (preFixed f)) = sInf (preFixed f) :=
  le_antisymm (sInf_prefixed_le f hf) (sInf_le_sInf_prefixed f hf)
