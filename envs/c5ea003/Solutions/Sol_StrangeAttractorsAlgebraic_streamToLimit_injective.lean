-- Prove2me | solution 1 for StrangeAttractorsAlgebraic.streamToLimit_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:42.789969+00:00
-- url     : https://prove2.me/submissions/6ca21514-ced3-4e86-83cf-d8405d446f46

-- Sol generated from Novelty/StrangeAttractorsAlgebraic.lean
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorsAlgebraic

/-!
# Finite graph approximants and a Cantor inverse limit

Binary de Bruijn graphs give a concrete finite directed-graph model for symbolic
dynamics.  Vertices at level `n` are binary words of length `n + 1`; an edge
records a one-symbol left shift.  Deleting the final symbol is a bonding map of
directed graphs.  Compatible finite prefixes form an inverse limit, and every
infinite binary stream determines a distinct point of that limit.
-/

open StrangeAttractorsAlgebraic











open StrangeAttractorsAlgebraic in
theorem solution: Function.Injective streamToLimit := by
  intro s t h
  ext n
  have := congr_arg Subtype.val h
  have h' := congr_fun (congr_fun this (n + 1)) ⟨n, Nat.lt_succ_self n⟩
  simp at h'
  exact h'
