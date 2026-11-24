-- Prove2me | Theorems.Thm_main3
-- name    : main3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:17:56.346966+00:00
-- url     : https://prove2.me/theorems/a5b33c85-cc01-4374-b196-b1c9b5bde2d4
-- title:
--   main3: main3
-- statement:
--   The main3 construction uses the main3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter3.lean#L478-L490
-- source:
--   https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter3.lean#L478-L490

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3
set_option autoImplicit true

theorem main3 (n : ℕ) (hn: n≠ 0) : ∃ (g : ℕ × ℕ → ℚ) (_ : arith_fp g n), ∃ (b : ℕ × ℕ ), (∀ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∀ (a : ℕ × ℕ),
(f a ≥ g b → f a = g b)) ∧ g b = Nat.fib n := by sorry
