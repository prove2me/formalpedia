-- Prove2me | Definitions.Def_Combinatorics_SingmasterFibonacci
-- name    : Combinatorics_SingmasterFibonacci
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:49:21.381167+00:00
-- url     : https://prove2.me/theorems/7beafdc8-6e0d-4435-a1cd-a5eaa7bbf1da
-- title:
--   Aether Catalog definitions — Combinatorics_SingmasterFibonacci
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.SingmasterFibonacci`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/SingmasterFibonacci.lean by skeleton subtraction
import Mathlib
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

namespace Singmaster

/-! ## The cross-row identity -/


/-! ## Cassini's identity at odd index -/


/-! ## The Fibonacci solutions -/

section Family

variable (i : ℕ)

/-- The row index of the `i`-th member of the family: `F_{2i+4} · F_{2i+5}`
(`15, 104, 714, 4895, …`). -/
def famRow (i : ℕ) : ℕ := Nat.fib (2 * i + 4) * Nat.fib (2 * i + 5)

/-- The column index of the `i`-th member of the family: `F_{2i+2} · F_{2i+5}`
(`5, 39, 272, 1869, …`). -/
def famCol (i : ℕ) : ℕ := Nat.fib (2 * i + 2) * Nat.fib (2 * i + 5)

/-- The `i`-th six-fold value, `C(famRow i, famCol i)` (`3003, …`). -/
def famVal (i : ℕ) : ℕ := (famRow i).choose (famCol i)






end Family

/-! ## Six occurrences -/



end Singmaster


