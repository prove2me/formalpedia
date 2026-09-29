-- Prove2me | Theorems.Thm_mme_finset_uniform_positive_fiber_truncation
-- name    : mme_finset_uniform_positive_fiber_truncation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:03:05.070701+00:00
-- url     : https://prove2.me/theorems/51868d5b-7e37-4bcc-820d-50409021367e
-- title:
--   Uniform positive truncation preserves every finite fiber label
-- statement:
--   Let a finite set $E$ be partitioned by a label map $z:E\to\mathcal Z$. If every nonempty label fiber contains at least the same positive number $H$ of elements, then there is a subset $F\subseteq E$ which preserves every label and has exactly $H$ elements in each fiber:
--
--   $$
--   z(F)=z(E),\qquad |F\cap z^{-1}(c)|=H\quad(c\in z(F)).
--   $$
--
--   This is the deterministic common-fiber-size step in the coupled first hash. Once the probabilistic count supplies many surviving Z-labels with degree at least $H$, truncation produces literal uniform C-tensor fibers without any additional cardinality loss.
-- source:
--   Finite uniformization step implicit in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271, where retained Z-blocks are truncated to a common positive multiplicity H before forming C-tensors over <1,H,1>; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

theorem mme_finset_uniform_positive_fiber_truncation
    {α ζ : Type} [DecidableEq α] [DecidableEq ζ]
    (E : Finset α) (z : α → ζ) (H : ℕ) (hH : 0 < H)
    (hmin : ∀ c ∈ E.image z,
      H ≤ (E.filter (fun e => z e = c)).card) :
    ∃ F : Finset α,
      F ⊆ E ∧
      F.image z = E.image z ∧
      ∀ c ∈ F.image z,
        (F.filter (fun e => z e = c)).card = H := by sorry
