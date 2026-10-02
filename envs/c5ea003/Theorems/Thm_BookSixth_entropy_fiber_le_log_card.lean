-- Prove2me | Theorems.Thm_BookSixth_entropy_fiber_le_log_card
-- name    : BookSixth.entropy_fiber_le_log_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T07:28:37.206522+00:00
-- url     : https://prove2.me/theorems/fb90a98b-d360-45b3-9790-8906024ca5fa
-- title:
--   Chapter 37 adapter: fiber entropy bounded by log support size
-- statement:
--   Per-row revelation bound: the entropy of one fiber of a joint distribution, -sum w_b log(w_b/P), is at most P*log|support|. Averages over rows give the per-step entropy cost in the Bregman-Minc route.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, per-row entropy bound for the entropy route to Bregman-Minc, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.entropy_fiber_le_log_card (β : Type*) [Fintype β] [Nonempty β] (w : β → ℝ) (P : ℝ)
    (hP : 0 < P) (hnn : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = P) :
    -∑ b, w b * Real.log (w b / P) ≤ P * Real.log (Fintype.card β) := by sorry
