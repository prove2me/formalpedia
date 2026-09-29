-- Prove2me | Theorems.Thm_ArgKernelGame_exists_unique_kernel
-- name    : ArgKernelGame.exists_unique_kernel
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:49.034337+00:00
-- url     : https://prove2.me/theorems/85a58917-18b0-4f90-b846-9174eef85d08
-- title:
--   Exists unique kernel
-- statement:
--   Formal statement of `ArgKernelGame.exists_unique_kernel` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ArgKernelGame.exists_unique_kernel(M : A → A → Prop) (hwf : WellFounded (flip M)) :
--       ∃! S : Set A, Kernel M S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ArgumentationKernelGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ArgumentationKernelGame.lean#L189

-- Thm stub generated from Novelty/ArgumentationKernelGame.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationKernelGame

/-!
# The topology of argumentation, X: the kernel/game bridge

This file is **self-contained** and builds a cross-domain bridge connecting three
areas that are usually developed independently:

* **Dung argumentation semantics** — *stable extensions* of an argumentation
  framework `(A, R)` (`R a b` reads "`a` attacks `b`").
* **Digraph theory** — *kernels* of a directed graph (an independent, absorbing
  set), a notion going back to von Neumann and Morgenstern.
* **Combinatorial game theory** — the set of *P-positions* (losing positions for
  the player to move) of the game whose move relation is `M` (`M p q` reads
  "from `p` one may move to `q`").

The unifying observation is elementary but load-bearing:

> A **stable extension** of the attack relation `R` is exactly a **kernel** of the
> transposed digraph `flip R`, which is exactly the **P-position set** of the game
> with move relation `flip R`.

Building on this dictionary we prove genuinely non-definitional results:

## The dictionary

* `stable_iff_kernel`        — stable extensions of `R` = kernels of `flip R`.
* `stable_iff_gameSolution`  — stable extensions of `R` = solutions (P-position
  sets) of the reversed-attack game.
* `terminal_mem_of_kernel`   — terminal positions are always losing (in the
  kernel): the normal-play convention falls out of the kernel axioms.

## Non-existence: the odd cycle

* `no_kernel_cyc3` / `no_stable_cyc3` — **the directed 3-cycle has no kernel and
  the 3-cycle framework has no stable extension.**  This is the classical
  obstruction (odd cycles) and explains why, with *no* well-foundedness
  hypothesis, stable extensions need not exist — in contrast to the maximal
  (preferred) extensions of the earlier cycles, which always exist.

## Well-founded existence and uniqueness (Zermelo determinacy)

For a **well-founded** move relation the game is *determined*: there is a unique
P-position set, computed by the standard game recursion "a position is losing iff
every move leads to a winning position".

* `isLoss`                   — the P-position predicate via well-founded recursion.
* `isLoss_iff`               — its defining fixed-point equation.
* `kernel_isLoss`            — the P-positions form a kernel.
* `kernel_unique`            — a well-founded digraph has at most one kernel.
* `exists_unique_kernel`     — **a well-founded digraph has a unique kernel.**
* `wf_game_determined`       — **every well-founded game has a unique solution**
  (a determinacy theorem in the spirit of Zermelo).
* `exists_unique_stable_of_wf` — **a well-founded argumentation framework has a
  unique stable extension.**  Existence of stable extensions, which fails on the
  odd cycle, is *restored* by well-foundedness.
-/

open ArgKernelGame

open Function

variable {A : Type*}

/-! ## Argumentation semantics (self-contained) -/



/-! ## Digraph kernels -/




/-! ## Combinatorial games -/


/-! ## The dictionary -/

/-
**Bridge (argumentation ⋈ graph theory).**  A set is a stable extension of the
attack relation `R` iff it is a kernel of the transposed digraph `flip R`.
-/


/-
**Terminal positions are losing.**  A position with no outgoing move must lie
in every kernel — the normal-play convention "no move ⇒ you lose" is forced by the
kernel axioms rather than assumed.
-/

/-! ## Non-existence on the odd cycle -/


/-
**The directed 3-cycle has no kernel.**  This is the classical odd-cycle
obstruction to kernel existence (von Neumann–Morgenstern / Richardson).
-/

/-
**The 3-cycle argumentation framework has no stable extension.**  Transported
across the dictionary, the odd-cycle obstruction says: with no well-foundedness
hypothesis, stable extensions can fail to exist.
-/

/-! ## Well-founded existence and uniqueness -/


/-
The defining fixed-point equation of `isLoss`.
-/

/-
**The P-positions form a kernel** of the move digraph: the game recursion
produces a genuine solution.
-/

/-
**A well-founded digraph has at most one kernel.**  Any kernel `S` agrees with
the P-position set, by well-founded induction along `flip M`.
-/

/-
**A well-founded digraph has a unique kernel.**
-/

theorem ArgKernelGame.exists_unique_kernel(M : A → A → Prop) (hwf : WellFounded (flip M)) :
    ∃! S : Set A, Kernel M S := by sorry
