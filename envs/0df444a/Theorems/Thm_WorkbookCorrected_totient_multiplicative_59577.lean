-- Prove2me | Theorems.Thm_WorkbookCorrected_totient_multiplicative_59577
-- name    : WorkbookCorrected.totient_multiplicative_59577
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:43:52.697882+00:00
-- url     : https://prove2.me/theorems/0665f4a7-f01c-477e-8845-cdfbfd604b08
-- title:
--   Euler's totient function is multiplicative
-- statement:
--   Euler's totient function $\varphi$ is multiplicative: for coprime positive $m,n$, $\varphi(mn)=\varphi(m)\varphi(n)$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_59577`, whose bare `φ` is not resolvable under its narrow `Mathlib.Analysis.Complex.Basic` preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_59577 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.totient_multiplicative_59577 : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → Nat.totient (m * n) = Nat.totient m * Nat.totient n := by sorry
