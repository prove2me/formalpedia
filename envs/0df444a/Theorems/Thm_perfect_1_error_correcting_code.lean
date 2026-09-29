-- Prove2me | Theorems.Thm_perfect_1_error_correcting_code
-- name    : perfect_1_error_correcting_code
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:50:58.440404+00:00
-- url     : https://prove2.me/theorems/0de925cf-6a84-424c-bce6-ce0f4ff97242
-- statement:
--   Classification of perfect 1-error-correcting codes: A perfect code of length n over alphabet q achieves the Hamming bound exactly. Known perfect codes: repetition codes, Hamming codes (n = (qᵏ-1)/(q-1)), and binary Golay code (n=23). The classification for general n and q is open; Tietäväinen (1973) proved no other perfect codes exist for q prime power.
-- source:
--   https://en.wikipedia.org/wiki/Hamming_bound

import Mathlib

import Mathlib

theorem perfect_1_error_correcting_code (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : 2 ≤ q) :
    (∃ (C : Finset (Fin n → Fin q)),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0) ∧
      (Finset.univ (α := Fin n → Fin q)).card ≤ C.card * (1 + n * (q - 1))) ↔
    ∃ k : ℕ, n = (q ^ k - 1) / (q - 1) := by
  sorry
