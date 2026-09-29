-- Prove2me | Theorems.Thm_RamseyTheory_arrows_step
-- name    : RamseyTheory.arrows_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:48.683971+00:00
-- url     : https://prove2.me/theorems/a9277df9-306d-489e-9e5a-a5b16b2c5517
-- title:
--   Erdős–Szekeres inductive step.
-- statement:
--   **Erdős–Szekeres inductive step.**
--   If `m → (s, t+1)` and `n → (s+1, t)` then `(m + n) → (s+1, t+1)`.
--
--   Proof: in a colouring of `W` with `|W| ≥ m + n`, pick a vertex `v`.  Split the
--   remaining vertices according to the colour of their edge to `v`: the red
--   neighbours `R` and the blue neighbours `B` satisfy `|R| + |B| ≥ m + n - 1`, so
--   `|R| ≥ m` or `|B| ≥ n`.  In the first case `R → (s, t+1)` gives a blue
--   `(t+1)`‑clique (done) or a red `s`‑clique, which together with `v` yields a red
--   `(s+1)`‑clique.  The second case is symmetric.
--
--   ```lean
--   theorem RamseyTheory.arrows_step{m n s t : ℕ} (hmpos : 0 < m) (hnpos : 0 < n)
--       (hm : Arrows m s (t + 1)) (hn : Arrows n (s + 1) t) :
--       Arrows (m + n) (s + 1) (t + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/Ramsey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/Ramsey.lean#L56

-- Thm stub generated from Applications/Combinatorics/Ramsey.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_Ramsey
/-
# Finite two‑colour Ramsey theory

This file develops the elementary theory of finite two‑colour Ramsey numbers,
culminating in the exact value `R(3,3) = 6` and the Erdős–Szekeres binomial
upper bound `R(s+1, t+1) ≤ C(s+t, s)`.

A *two‑colouring* of a complete graph is encoded by a single `SimpleGraph G`:
the edges of `G` are the **red** edges and the edges of its complement `Gᶜ`
are the **blue** edges.  A red clique is then a clique of `G` and a blue clique
is a clique of `Gᶜ`.

The central relation is the *arrow* relation `Arrows n s t`
(classically written `n → (s, t)`): every red/blue colouring of any vertex set
of size at least `n` contains a red `s`‑clique or a blue `t`‑clique.
-/


open scoped Classical
open SimpleGraph Finset

open RamseyTheory

/-! ## Core combinatorial objects -/



/-! ## Monotonicity -/


/-! ## The Erdős–Szekeres recursion -/

theorem RamseyTheory.arrows_step{m n s t : ℕ} (hmpos : 0 < m) (hnpos : 0 < n)
    (hm : Arrows m s (t + 1)) (hn : Arrows n (s + 1) t) :
    Arrows (m + n) (s + 1) (t + 1) := by sorry
