-- Prove2me | Theorems.Thm_Singmaster_six_le_mult_fib
-- name    : Singmaster.six_le_mult_fib
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:32:49.596962+00:00
-- url     : https://prove2.me/theorems/a1c056ce-0ae2-4dcf-92e4-44bfb9ef7f8d
-- title:
--   Every member of the Fibonacci family occurs at least six times.
-- statement:
--   **Every member of the Fibonacci family occurs at least six times.**
--
--   The value `t = C(F_{2i+4}F_{2i+5}, F_{2i+2}F_{2i+5})` sits at the six positions
--   `(t,1)`, `(t,t-1)`, `(n,k)`, `(n,n-k)`, `(n-1,k+1)`, `(n-1,n-k-2)`
--   where `n = famRow i` and `k = famCol i`.
--
--   ```lean
--   theorem Singmaster.six_le_mult_fib(i : ℕ) : 6 ≤ mult (famVal i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterFibonacci.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterFibonacci.lean#L167

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


/-! ## Cassini's identity at odd index -/


/-! ## The Fibonacci solutions -/


variable (i : ℕ)










/-! ## Six occurrences -/

theorem Singmaster.six_le_mult_fib(i : ℕ) : 6 ≤ mult (famVal i) := by sorry
