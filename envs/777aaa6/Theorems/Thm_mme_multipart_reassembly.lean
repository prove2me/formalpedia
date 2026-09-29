-- Prove2me | Theorems.Thm_mme_multipart_reassembly
-- name    : mme_multipart_reassembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T06:24:39.748701+00:00
-- url     : https://prove2.me/theorems/12abff1a-11b2-496c-9849-6f8f953811d3
-- title:
--   Per-part conditions reassemble into global ones
-- statement:
--   Conditions certified part by part reassemble into the same condition stated globally.
--
--   If every part keeps its own share of a histogram within its own tolerance, then the total is within
--   the sum of the tolerances of the sum of the shares. And if every part fixes the grade of each of its
--   blocks, then every block has its grade fixed, since each block belongs to exactly one part.
--
--   These are the two halves of what a stage node needs from its parts in order to conclude the
--   condition it was asked to establish.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Theorems.Thm_mme_multipart_card_split

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem mme_multipart_reassembly :
    (∀ {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop)
      (target e : Fin p → ℝ),
      (∀ j, |(Fintype.card {b : B // part b = j ∧ P b} : ℝ) - target j| ≤ e j) →
      |(Fintype.card {b : B // P b} : ℝ) - ∑ j, target j| ≤ ∑ j, e j) ∧
    ∀ {B : Type u} {p : ℕ} (part : B → Fin p) (Q : B → Prop),
      (∀ j, ∀ b, part b = j → Q b) → ∀ b, Q b := by sorry
