-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_MerkleCommitment
-- name    : Cryptography_ZeroKnowledge_MerkleCommitment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:29:54.367125+00:00
-- url     : https://prove2.me/theorems/bd2d3717-5a89-408a-bb72-93cb95793bc4
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_MerkleCommitment
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.MerkleCommitment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/MerkleCommitment.lean by skeleton subtraction
import Mathlib

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

namespace ZK.MerkleCommitment

open Function

variable {α : Type*}

/-- The Merkle root of a complete binary tree of depth `d` whose leaves are indexed
by bit-string addresses `Fin d → Bool`. At depth `d+1` the first address bit selects
the left (`false`) vs. right (`true`) subtree, and `h` folds the two subtree roots. -/
def mroot (h : α → α → α) : (d : ℕ) → ((Fin d → Bool) → α) → α
  | 0, f => f Fin.elim0
  | d + 1, f => h (mroot h d (fun p => f (Fin.cons false p)))
                  (mroot h d (fun p => f (Fin.cons true p)))

/-- An explicit collision of the compression function `h`: two *distinct* input
pairs with equal images. Under collision-resistance such a witness is infeasible to
find, so every theorem below whose conclusion is `HasCollision h` is a constructive
reduction of ambiguity to breaking `h`. -/
def HasCollision (h : α → α → α) : Prop :=
  ∃ a b a' b', h a b = h a' b' ∧ (a, b) ≠ (a', b')

/-! ## Binding of the Merkle root -/



/-! ## Authentication paths: opening a single committed step -/

/-- The honest authentication path for the leaf at address `path`: the list of
*sibling* subtree digests encountered on the way from the root to the leaf. -/
def authPath (h : α → α → α) :
    (d : ℕ) → (path : Fin d → Bool) → ((Fin d → Bool) → α) → (Fin d → α)
  | 0, _, _ => Fin.elim0
  | d + 1, path, f =>
      Fin.cons
        (mroot h d (fun p => f (Fin.cons (!(path 0)) p)))
        (authPath h d (Fin.tail path) (fun p => f (Fin.cons (path 0) p)))

/-- The verifier's root recomputation from a claimed `leaf` value at address `path`
together with a supplied list of sibling digests `sibs`: fold `h` up the path,
placing the sibling on the correct side dictated by each address bit. -/
def recompute (h : α → α → α) : (d : ℕ) → (path : Fin d → Bool) → α → (Fin d → α) → α
  | 0, _, leaf, _ => leaf
  | d + 1, path, leaf, sibs =>
      let child := recompute h d (Fin.tail path) leaf (Fin.tail sibs)
      if path 0 = false then h child (sibs 0) else h (sibs 0) child



end ZK.MerkleCommitment


