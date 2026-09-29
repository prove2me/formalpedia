-- Prove2me | solution 1 for ArgKernelGame.exists_unique_kernel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:47:21.650194+00:00
-- url     : https://prove2.me/submissions/99e16ff5-ad08-48ff-b4e1-6e43121d363b

-- Sol generated from Novelty/ArgumentationKernelGame.lean
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
theorem isLoss_iff (M : A → A → Prop) (hwf : WellFounded (flip M)) (a : A) :
    isLoss M hwf a ↔ ∀ b, M a b → ¬ isLoss M hwf b := by
  rw [ isLoss ];
  grind +suggestions

/-
**The P-positions form a kernel** of the move digraph: the game recursion
produces a genuine solution.
-/
theorem kernel_isLoss (M : A → A → Prop) (hwf : WellFounded (flip M)) :
    Kernel M {a | isLoss M hwf a} := by
  unfold Kernel;
  simp +decide [ Independent, Absorbing ];
  grind +suggestions

/-
**A well-founded digraph has at most one kernel.**  Any kernel `S` agrees with
the P-position set, by well-founded induction along `flip M`.
-/
theorem kernel_unique (M : A → A → Prop) (hwf : WellFounded (flip M)) {S : Set A}
    (hS : Kernel M S) : S = {a | isLoss M hwf a} := by
  ext a;
  induction' a using hwf.induction with a ih;
  rw [ Set.mem_setOf_eq, isLoss_iff ];
  constructor;
  · exact fun ha b hb => fun hb' => hS.1 a ha b ( ih b hb |>.2 hb' ) hb;
  · exact fun h => Classical.not_not.1 fun ha => by obtain ⟨ b, hbS, hb ⟩ := hS.2 a ha; specialize ih b hb; aesop;

/-
**A well-founded digraph has a unique kernel.**
-/


/-
**A well-founded argumentation framework has a unique stable extension.**
Well-foundedness of the attack relation restores the existence of stable
extensions that failed on the odd cycle (`no_stable_cyc3`), and forces uniqueness.
-/


open ArgKernelGame in
theorem solution(M : A → A → Prop) (hwf : WellFounded (flip M)) :
    ∃! S : Set A, Kernel M S := by
  refine' ⟨ _, ⟨ kernel_isLoss M hwf, fun S hS => kernel_unique M hwf hS ⟩ ⟩
