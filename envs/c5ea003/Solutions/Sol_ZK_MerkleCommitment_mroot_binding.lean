-- Prove2me | solution 1 for ZK.MerkleCommitment.mroot_binding
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:54:24.648549+00:00
-- url     : https://prove2.me/submissions/ad0be23d-8d21-43fe-8fc0-6972df96b08e

-- Sol generated from Cryptography/ZeroKnowledge/MerkleCommitment.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_MerkleCommitment

/-!
# Merkle-Tree Commitments for Zero-Knowledge Theorem Proving

The zero-knowledge theorem-proving protocol of the mission begins with step (1):
*the prover commits to each proof step using a collision-resistant hash*. The
standard device that makes this scale — a prover with an `n`-step proof publishes
a single short digest, yet can later open **any one** challenged step succinctly —
is the **Merkle tree**.

This file formalizes Merkle commitments over a complete binary tree of depth `d`,
whose `2^d` leaves are indexed by bit-strings `Fin d → Bool` (a leaf address is a
top-down list of left/right choices). A two-argument *compression function*
`h : α → α → α` folds child digests into parent digests. The salient
cryptographic contents are:

* **Binding of the root** (`mroot_binding`): if two different leaf assignments
  hash to the *same* Merkle root, then `h` has an explicit collision. Hence, under
  collision-resistance, the root binds the prover to a unique proof.
* **Perfect binding** (`mroot_injective`): if `h` is (jointly) injective — an
  idealized collision-free hash — the Merkle root is an injective function of the
  leaves, so the commitment determines the committed proof uniquely.
* **Opening completeness** (`recompute_auth`): the honest authentication path for
  a leaf (the sibling digests along its root path) recomputes exactly the true
  root. This is protocol step (3): "the prover opens that step."
* **Opening binding** (`path_binding`): if two authentication paths for the *same*
  leaf address recompute to the same root but claim *different* leaf values, then
  `h` again has an explicit collision. So a challenged step cannot be opened two
  ways — the verifier's single-step check is meaningful.

Together these say: the Merkle root is a succinct, binding commitment to the whole
proof, and each opened step is itself bound — exactly the properties the
zero-knowledge theorem-proving protocol relies on, with all "collision-resistance"
uses made explicit as constructed collisions.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): A hash-tree digest should be *binding* precisely to the
extent `h` is collision-resistant: any ambiguity in the committed leaves must
"surface" as a collision at some internal node on the divergence path. Two
surprising sub-claims: (a) binding holds with **no** algebraic assumption on `h`
whatsoever — the collision is *constructed*, not assumed away; (b) the same
inductive extractor handles both the global root and a single opened leaf.

Experiment (Experimenter): Modeled leaves as `f : (Fin d → Bool) → α` and defined
`mroot` by recursion on depth, splitting on the *first* address bit via `Fin.cons`.
Verified on depth 0 (root = the unique leaf, so equal roots ⟹ equal leaves) and the
inductive step: equal roots either collide at the top node (distinct child pairs) or
force equal child digests, whereupon `f ≠ g` pushes the divergence into one subtree
and the induction hypothesis manufactures the collision. The opening machinery
(`authPath`, `recompute`) was checked to satisfy `recompute_auth` by the same
first-bit case split, and `path_binding` reuses the identical top-node dichotomy.

Analysis (Analyst): The load-bearing fact is structural, not arithmetic: a compression
tree is binding "for free," and the security assumption (collision-resistance) enters
only when one wants to *conclude* uniqueness (`mroot_injective`). The reduction is
fully constructive — it names the colliding inputs — which is exactly what a soundness
extractor needs. Failure mode considered and avoided: indexing leaves by `Fin (2^d)`
forces awkward `Nat` arithmetic in the split; bit-string addresses with `Fin.cons`
make the recursion definitional.

Critique (Critic): None of the four results is `True`-shaped or `decide`-closed:
each returns/《consumes》an explicit collision witness or an injectivity statement, and
each proof is a genuine `induction` on depth with a nontrivial case dichotomy. The
binding theorems are non-vacuous for every `d` (for `d = 0` the "collision" branch is
unreachable and the leaf-equality branch does the work, which is the honest content).

Synthesis (PI): Root binding + perfect binding + opening completeness + opening
binding = a complete, assumption-free account of why a Merkle commitment lets a
prover commit to an entire proof with one digest yet be held to every opened step.
-- !-- Lab Notes -- !--
-/

open ZK.MerkleCommitment

open Function

variable {α : Type*}



/-! ## Binding of the Merkle root -/



/-! ## Authentication paths: opening a single committed step -/






open ZK.MerkleCommitment in
theorem solution(h : α → α → α) : ∀ (d : ℕ) (f g : (Fin d → Bool) → α),
    mroot h d f = mroot h d g → f ≠ g → HasCollision h := by
  intro d
  induction d with
  | zero =>
    intro f g hr hne
    exfalso; apply hne
    funext p
    have : p = Fin.elim0 := by funext i; exact i.elim0
    subst this; simpa [mroot] using hr
  | succ d ih =>
    intro f g hr hne
    simp only [mroot] at hr
    set F0 := mroot h d (fun p => f (Fin.cons false p))
    set F1 := mroot h d (fun p => f (Fin.cons true p))
    set G0 := mroot h d (fun p => g (Fin.cons false p))
    set G1 := mroot h d (fun p => g (Fin.cons true p))
    by_cases hcol : (F0, F1) = (G0, G1)
    · rw [Prod.mk.injEq] at hcol
      obtain ⟨e0, e1⟩ := hcol
      have hrest : (fun p => f (Fin.cons false p)) ≠ (fun p => g (Fin.cons false p)) ∨
                   (fun p => f (Fin.cons true p)) ≠ (fun p => g (Fin.cons true p)) := by
        by_contra hc
        push_neg at hc
        obtain ⟨hcf, hct⟩ := hc
        apply hne
        funext p
        have hp : p = Fin.cons (p 0) (Fin.tail p) := (Fin.cons_self_tail p).symm
        rw [hp]
        cases hb : p 0
        · exact congrFun hcf (Fin.tail p)
        · exact congrFun hct (Fin.tail p)
      rcases hrest with hr0 | hr1
      · exact ih _ _ e0 hr0
      · exact ih _ _ e1 hr1
    · exact ⟨F0, F1, G0, G1, hr, hcol⟩
