-- Prove2me | Theorems.Thm_Singmaster_choose_cross
-- name    : Singmaster.choose_cross
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:31:22.448778+00:00
-- url     : https://prove2.me/theorems/27958ecd-623a-4960-bf5c-55ec3649f6af
-- title:
--   Cross-row identity.
-- statement:
--   **Cross-row identity.**  Write `N = j + m`.  If `(N+1)(j+2) = m(m-1)` then the entry
--   `C(N+1, j+1)` repeats one row higher as `C(N, j+2)`.
--
--   This is the factorial identity `n(k+1) = (n-k)(n-k-1)` in subtraction-free form
--   (`n = N+1`, `k = j+1`, `m = n-k`).
--
--   ```lean
--   theorem Singmaster.choose_cross{j m : ℕ} (hm : 2 ≤ m)
--       (h : (j + m + 1) * (j + 2) = m * (m - 1)) :
--       (j + m + 1).choose (j + 1) = (j + m).choose (j + 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterFibonacci.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterFibonacci.lean#L37

-- Thm stub generated from Combinatorics/SingmasterFibonacci.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
/-
# The Fibonacci family behind the "six times" phenomenon

Building on `Combinatorics.SingmasterOccurrences`, this file explains *why* infinitely
many numbers occur at least six times in Pascal's triangle.

The mechanism is a bridge between three different pieces of mathematics:

* **Combinatorics.**  A value `C(n,k)` normally occupies four positions —
  `(n,k)`, `(n,n-k)`, `(t,1)`, `(t,t-1)` where `t = C(n,k)`.  Two *extra* positions
  appear exactly when the same number also occurs one row higher, i.e. when
  `C(n,k) = C(n-1,k+1)`.
* **Arithmetic.**  Clearing factorials turns that coincidence into the Diophantine
  equation `n (k+1) = (n-k)(n-k-1)` (`Singmaster.choose_cross`).
* **The Fibonacci recursion.**  That equation is a disguised Pell equation, and
  Cassini's identity `F_{2i+3}^2 = F_{2i+2} F_{2i+4} + 1` produces an infinite family
  of solutions `n = F_{2i+4} F_{2i+5}`, `k = F_{2i+2} F_{2i+5}`.

For `i = 0` this is `n = 15`, `k = 5`, giving `C(15,5) = C(14,6) = 3003`; the next
member is `n = 104`, `k = 39`, giving `C(104,39) = C(103,40)`.

Main results:
* `Singmaster.choose_cross` — the cross-row identity from the Diophantine condition;
* `Singmaster.cassini_odd` — Cassini's identity at odd index, over `ℕ`;
* `Singmaster.fib_cross` — the Fibonacci solutions of the Diophantine condition;
* `Singmaster.six_le_mult_fib` — every member of the family occurs at least six times;
* `Singmaster.infinitely_many_six` — hence there are arbitrarily large such numbers.
-/

open Finset

open Singmaster

/-! ## The cross-row identity -/

theorem Singmaster.choose_cross{j m : ℕ} (hm : 2 ≤ m)
    (h : (j + m + 1) * (j + 2) = m * (m - 1)) :
    (j + m + 1).choose (j + 1) = (j + m).choose (j + 2) := by sorry
