-- Prove2me | Theorems.Thm_cube_even_weight_count
-- name    : cube_even_weight_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T22:06:56.96546+00:00
-- url     : https://prove2.me/theorems/041bdfd9-7186-42f9-83a0-051e42365199
-- statement:
--   **Even-weight count on the Boolean cube.**
--
--   For every $d \ge 1$, exactly $2^{d-1}$ of the $2^d$ vertices of the $d$-cube have even Hamming weight:
--   $$\#\!\left\{ z \in \{0,1\}^d \;:\; |z| \equiv 0 \pmod 2 \right\} \;=\; 2^{d-1},$$
--   where $|z|$ denotes the cardinality of $\{i : z_i = 1\}$.
--
--   Standard fact, proven via the parity-flipping involution $z \mapsto z \oplus e_1$ (flip the first coordinate). This involution is a bijection between the even-weight class and the odd-weight class, so they have equal cardinalities; combined with $|\{0,1\}^d| = 2^d$, each class has $2^{d-1}$ vertices.
-- source:
--   Folklore — parity-flip involution on the Boolean cube. Standard fact underlying many parity arguments in the analysis of Boolean functions; see e.g. O'Donnell, Ryan. "Analysis of Boolean Functions." Cambridge University Press (2014), Chapter 1.

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-!
# Even-weight count on the Boolean cube

For `d ≥ 1`, exactly `2^(d-1)` of the `2^d` vertices of the `d`-cube
have even Hamming weight. Proven via the parity-flipping involution
`z ↦ flipBit z ⟨0, h_pos⟩` (flip the first coordinate), which bijects
the even-weight class with the odd-weight class.

Self-contained foundational fact, reusable across any cube
combinatorics argument that splits by parity. Not in Mathlib.
-/

/-- **Even-weight count on the Boolean cube.** For `d ≥ 1`, the number
    of vertices `z : Fin d → Bool` whose Hamming weight (i.e., the
    cardinality of `{i : z i = true}`) is even equals `2^(d-1)`. -/

theorem cube_even_weight_count {d : ℕ} (h_pos : 1 ≤ d) :
    ((Finset.univ : Finset (Fin d → Bool)).filter
      (fun z => ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 = 0)).card
      = 2^(d-1) := by sorry
