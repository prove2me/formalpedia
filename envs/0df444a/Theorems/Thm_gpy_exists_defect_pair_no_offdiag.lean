-- Prove2me | Theorems.Thm_gpy_exists_defect_pair_no_offdiag
-- name    : gpy_exists_defect_pair_no_offdiag
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T01:45:47.557076+00:00
-- url     : https://prove2.me/theorems/9f4dd1ba-9f9e-47bd-a7c5-827079a81e7b
-- title:
--   Counterexample: defect with no off-diagonal coordinate
-- statement:
--   Over Fin 1, the pair h = 0, d = 2, e = 1 is compatible and not good, yet every coordinate equals the distinguished one, so there is no j different from i and no off-diagonal difference at all. The defect prime 2 comes from the i-coordinate modulus itself. This is a counterexample to the unqualified claim that a defect pair's prime divides some difference h_i - h_j with j different from i, and nothing more. Formalization Note: compatibility and goodness are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_exists_defect_pair_no_offdiag :
    ∃ h d e : Fin 1 → ℕ, ∃ i : Fin 1,
      (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
        h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
      ∀ j : Fin 1, j = i := by sorry
