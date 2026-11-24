-- Prove2me | Theorems.Thm_main2
-- name    : main2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:17:51.953172+00:00
-- url     : https://prove2.me/theorems/0099918e-204a-458b-8600-09750cfc03ea
-- title:
--   main2: main2
-- statement:
--   The main2 construction uses the main2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter3.lean#L420-L476
-- source:
--   https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter3.lean#L420-L476

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3
set_option autoImplicit true

theorem main2 (n : ℕ) (hn : n ≠ 0) : ∃ (f : ℕ × ℕ → ℚ) (hf : arith_fp f n), ∃ (a : ℕ × ℕ), f a = Nat.fib n := by sorry
