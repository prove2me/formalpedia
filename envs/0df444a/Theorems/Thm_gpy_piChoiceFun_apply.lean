-- Prove2me | Theorems.Thm_gpy_piChoiceFun_apply
-- name    : gpy_piChoiceFun_apply
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:38:11.917465+00:00
-- url     : https://prove2.me/theorems/570f7550-7294-49da-ac02-0b8173f8b8b9
-- title:
--   The pi-type choice function agrees with the choice on the finset
-- statement:
--   The plain function underlying a pi-type element agrees with the given choice function at every prime in the finset, and is (none, none) elsewhere. Formalization Note: the function is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_piChoiceFun_apply {k : ℕ} {s : Finset ℕ}
    {f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)} {p : ℕ} (hp : p ∈ s) :
    (if hp' : p ∈ s then f p hp' else (none, none)) = f p hp  := by sorry
