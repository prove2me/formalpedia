-- Prove2me | Theorems.Thm_d9Revenue_measurable_comp
-- name    : d9Revenue_measurable_comp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:51.771192+00:00
-- url     : https://prove2.me/theorems/9432f43d-876d-4342-bd04-d262febdd1ca
-- title:
--   d9Revenue_measurable_comp
-- statement:
--   Automatically extracted helper theorem d9Revenue_measurable_comp from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_measurable_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => revenue f p (fun i => X i ω) k (s ω)) := by sorry
