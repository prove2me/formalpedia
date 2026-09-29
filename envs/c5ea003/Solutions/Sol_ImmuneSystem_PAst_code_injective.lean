-- Prove2me | solution 1 for ImmuneSystem.PAst.code_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:27:28.186408+00:00
-- url     : https://prove2.me/submissions/ed03aa4a-abdb-4990-b3ee-d4f68f10c673

-- Sol generated from Shared/ImmuneAstCore.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore

/-!
# Algorithmic Immune System, Part I: the parasite calculus and structural attestation

This file sets up the syntactic layer of an *algorithmic immune system*: a runtime
that guards a program against arbitrary, unknown, self-modifying mutations of its
own abstract syntax tree.

The object language `PAst` (*parasite calculus*) is deliberately minimal but has
exactly the three ingredients that make self-modifying malware possible:

* `PAst.inp` — the *self register*.  At top level the runtime feeds a program its
  own source code (Section II), so `inp` is a genuine quine primitive: a program
  can read (and reason about) its own AST.
* `PAst.call f a` — invocation of a *fixed subprogram* `f` on a computed argument.
  This lets a parasite invoke a detector on itself.
* `PAst.attack` — the single observable, forbidden side effect.

`PAst.ite` gives branching and `PAst.lit` constants.

The main results here are purely structural and are the foundation of the
attestation mechanism used in Part III:

* `PAst.code_injective` : the Gödel numbering `PAst.code` is injective, so a
  structural attestation tag identifies an AST uniquely;
* `PAst.code_eq_iff`   : attestation equality is exactly AST equality;
* `PAst.size_pos`, `PAst.size_lt_of_mem_children` : the well-founded size measure
  used for the counting arguments in Part III.
-/

open ImmuneSystem


open PAst










@[simp] theorem code_lit (n : ℕ) : code (lit n) = 5 * n + 2 := rfl
@[simp] theorem code_ite (c a b : PAst) :
    code (ite c a b) = 5 * (Nat.pair (Nat.pair (code c) (code a)) (code b)) + 3 := rfl
@[simp] theorem code_call (f a : PAst) :
    code (call f a) = 5 * (Nat.pair (code f) (code a)) + 4 := rfl

open ImmuneSystem.PAst in
theorem solution: Function.Injective code := by
  intro s
  induction s with
  | inp =>
      intro t h
      cases t <;> simp_all [code]
  | attack =>
      intro t h
      cases t <;> simp_all [code]
  | lit n =>
      intro t h
      cases t with
      | lit m => simp only [code_lit] at h; simp; omega
      | _ => simp_all [code] <;> omega
  | ite c a b ihc iha ihb =>
      intro t h
      cases t with
      | ite c' a' b' =>
          simp only [code_ite] at h
          have hp : Nat.pair (Nat.pair (code c) (code a)) (code b)
              = Nat.pair (Nat.pair (code c') (code a')) (code b') := by omega
          rw [Nat.pair_eq_pair, Nat.pair_eq_pair] at hp
          obtain ⟨⟨h1, h2⟩, h3⟩ := hp
          rw [ihc h1, iha h2, ihb h3]
      | _ => simp_all [code] <;> omega
  | call f a ihf iha =>
      intro t h
      cases t with
      | call f' a' =>
          simp only [code_call] at h
          have hp : Nat.pair (code f) (code a) = Nat.pair (code f') (code a') := by omega
          rw [Nat.pair_eq_pair] at hp
          rw [ihf hp.1, iha hp.2]
      | _ => simp_all [code] <;> omega
