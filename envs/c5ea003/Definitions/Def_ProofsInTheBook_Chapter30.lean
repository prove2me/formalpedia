-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter30
-- name    : ProofsInTheBook_Chapter30
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T17:22:29.931886+00:00
-- url     : https://prove2.me/theorems/4da3d812-91ba-4067-821e-32e0fed50601
-- title:
--   Finite cancellation certificates and marked list-family path systems
-- statement:
--   The abstract cancellation certificate consists of a decidable bad predicate on a family type, a bijection of the bad subtype, an additive-group-valued weight, and the identity that the bijection negates the weight. Despite the name BadInvolutionCertificate, the structure requires a bijection and does not require its square to be the identity. It does not itself supply finiteness.
--
--   For a vertex weight v, a list has weight equal to the product of v over its entries, with repetitions counted and the empty product equal to 1. A good family consists of a permutation of n indices and n arbitrary vertex lists whose vertex sets are pairwise disjoint for distinct indices; even shared endpoints are excluded. Repetitions within a single list are allowed. A marked bad family consists of a permutation, distinct indices i,j, a shared vertex belonging to each of two prefix lists, two tail lists, and another list for every index. The shared vertex is only required to belong to the prefixes, not to be their final entry. No endpoint, adjacency, length bound, or compatibility constraint on the other lists is imposed.
--
--   The family type is the disjoint union of these two structures, and isBad selects its bad constructor. The unsigned weight of a good family is the product of all its list weights. For a bad family it is the product of the four prefix and tail weights and of every indexed other-list weight, including those at i and j. Multiplication by the permutation sign gives the signed weight. Tail-swap exchanges the two tails and composes the permutation with the transposition of i and j; the bundle includes proofs that this operation is involutive, preserves the specified unsigned weight, and reverses the signed weight. It thereby constructs a cancellation certificate for these marked data, without constructing a bijection to unmarked geometric paths.
--
--   A PathCountSystem over a commutative ring supplies finite types $P_{ij}$, their weights, a vertex weight, and a bijection
--   $$\coprod_{\sigma\in S_n}\prod_iP_{\sigma(i),i}\simeq\mathcal F_n(V).$$
--   It also supplies equality of the signed family weight with $\operatorname{sgn}(\sigma)\prod_i a(p_i)$ for every choice. Its matrix entry is the weighted finite sum over $P_{ij}$. These compatibility fields are assumptions on a system, not derived facts about a grid.
--
--   Finally, the retained empty-vertex example identifies $\mathcal F_2(\varnothing)$ with the two permutations: every list is empty and marked bad data cannot exist. This gives finite and decidable-equality instances in that special case. For positive n and nonempty V the unrestricted list family is not finite; the source expressly states that bounded/geometric path constructions and hook-length applications require additional infrastructure. These definitions therefore support conditional finite algebraic identities, not a completed geometric LGV formalization.
-- source:
--   Immutable original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L134 (cancellation certificate), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L245 (list weights and good families), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L263 (marked bad data), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L343 (disjoint-union family), and https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L435 (PathCountSystem). The explicit limitation and empty-vertex example begin at https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L578. Original bytes match the public commit; repository topic is “Lattice paths and determinants,” with no edition mapping asserted.

import Mathlib

/-!
# Chapter 30: Lattice paths and determinants

From "Proofs from THE BOOK":

**Lindström-Gessel-Viennot lemma**: The number of non-intersecting
lattice path systems from sources to sinks equals a determinant.

The book applies this to count standard Young tableaux and proves
the hook length formula: |SYT(λ)| = n! / ∏ hook_lengths.
-/

namespace ProofsInTheBook.Chapter30

open Matrix BigOperators













/--
A finite LGV cancellation certificate: `bad` identifies the bad path families,
`tauBad` pairs bad families, and `sign_reverse` says the signed weight reverses.
-/
structure BadInvolutionCertificate (Family R : Type*) [AddCommGroup R] where
  bad : Family → Prop
  bad_decidable : DecidablePred bad
  tauBad : {F : Family // bad F} ≃ {F : Family // bad F}
  signedWeight : Family → R
  sign_reverse : ∀ F : {F : Family // bad F}, signedWeight (tauBad F).1 = -signedWeight F.1

attribute [instance] BadInvolutionCertificate.bad_decidable





















/-- The product of vertex weights along a finite path. -/
def pathVertexWeight {V R : Type*} [CommMonoid R] (weight : V → R) (p : List V) : R :=
  (p.map weight).prod

/--
The good side of a concrete LGV path family: a permutation together with
pairwise disjoint vertex lists.
-/
structure LGVGoodFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V
  nonIntersecting :
    ∀ i j : Fin n, i ≠ j → Disjoint (paths i).toFinset (paths j).toFinset

/--
The bad side of a concrete LGV path family, with the Lindström tail-swap
data made explicit.  The two distinguished paths have prefixes ending at a
shared vertex and tails that can be exchanged.
-/
structure LGVBadFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  i : Fin n
  j : Fin n
  hij : i ≠ j
  shared : V
  leftPrefix : List V
  leftTail : List V
  rightPrefix : List V
  rightTail : List V
  left_shared : shared ∈ leftPrefix
  right_shared : shared ∈ rightPrefix
  otherPaths : Fin n → List V

namespace LGVBadFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]



/-- Swapping the two marked tails and multiplying the permutation by the same transposition. -/
def tailSwap (B : LGVBadFamily n V) : LGVBadFamily n V where
  perm := B.perm * Equiv.swap B.i B.j
  i := B.i
  j := B.j
  hij := B.hij
  shared := B.shared
  leftPrefix := B.leftPrefix
  leftTail := B.rightTail
  rightPrefix := B.rightPrefix
  rightTail := B.leftTail
  left_shared := B.left_shared
  right_shared := B.right_shared
  otherPaths := B.otherPaths

/-- Tail-swap is an involution on the marked bad data. -/
theorem tailSwap_tailSwap (B : LGVBadFamily n V) : B.tailSwap.tailSwap = B := by
  cases B
  simp [tailSwap, mul_assoc]

/-- Tail-swap changes the permutation sign. -/
theorem sign_tailSwap (B : LGVBadFamily n V) :
    Equiv.Perm.sign B.tailSwap.perm = -Equiv.Perm.sign B.perm := by
  simp [tailSwap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap B.hij]



/-- The unsigned vertex-weight product of a marked bad family. -/
def unsignedWeight [CommMonoid R] (weight : V → R) (B : LGVBadFamily n V) : R :=
  pathVertexWeight weight B.leftPrefix *
    pathVertexWeight weight B.leftTail *
    pathVertexWeight weight B.rightPrefix *
    pathVertexWeight weight B.rightTail *
    ∏ k, pathVertexWeight weight (B.otherPaths k)

/-- Swapping the marked tails preserves the unsigned product of vertex weights. -/
theorem unsignedWeight_tailSwap [CommMonoid R] (weight : V → R) (B : LGVBadFamily n V) :
    unsignedWeight weight B.tailSwap = unsignedWeight weight B := by
  simp [unsignedWeight, tailSwap, mul_assoc, mul_left_comm, mul_comm]

end LGVBadFamily

/--
Concrete LGV families split into non-intersecting families and marked
intersecting families.  The mark is exactly the local data needed for the
Lindström tail-swap involution.
-/
inductive LGVFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  | good (G : LGVGoodFamily n V)
  | bad (B : LGVBadFamily n V)

namespace LGVFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]

/-- The bad predicate for concrete LGV families. -/
def isBad : LGVFamily n V → Prop
  | good _ => False
  | bad _ => True

instance : DecidablePred (isBad (n := n) (V := V)) := by
  intro F
  cases F with
  | good _ => exact isFalse id
  | bad _ => exact isTrue trivial

/-- The permutation attached to a concrete LGV family. -/
def perm : LGVFamily n V → Equiv.Perm (Fin n)
  | good G => G.perm
  | bad B => B.perm



/-- The unsigned product of vertex weights for a concrete LGV family. -/
def unsignedWeight [CommMonoid R] (weight : V → R) : LGVFamily n V → R
  | good G => ∏ i, pathVertexWeight weight (G.paths i)
  | bad B => B.unsignedWeight weight

/-- The usual LGV signed weight: permutation sign times path-weight product. -/
def signedWeight [CommRing R] (weight : V → R) (F : LGVFamily n V) : R :=
  Equiv.Perm.sign F.perm • F.unsignedWeight weight

/-- Tail-swap on the subtype of marked bad concrete families. -/
def badTailSwap (F : {F : LGVFamily n V // isBad F}) : {F : LGVFamily n V // isBad F} :=
  match F with
  | ⟨good _, h⟩ => False.elim h
  | ⟨bad B, _⟩ => ⟨bad B.tailSwap, trivial⟩

/-- The marked tail-swap is an involution on bad concrete families. -/
theorem badTailSwap_badTailSwap (F : {F : LGVFamily n V // isBad F}) :
    badTailSwap (badTailSwap F) = F := by
  rcases F with ⟨F, hF⟩
  cases F with
  | good _ => contradiction
  | bad B =>
      simp [badTailSwap, LGVBadFamily.tailSwap_tailSwap]

/-- The bad-family equivalence induced by marked tail-swap. -/
def badTailSwapEquiv : {F : LGVFamily n V // isBad F} ≃ {F : LGVFamily n V // isBad F} where
  toFun := badTailSwap
  invFun := badTailSwap
  left_inv := badTailSwap_badTailSwap
  right_inv := badTailSwap_badTailSwap

/-- Marked tail-swap reverses the signed vertex weight. -/
theorem signedWeight_badTailSwap [CommRing R] (weight : V → R)
    (F : {F : LGVFamily n V // isBad F}) :
    signedWeight weight (badTailSwapEquiv F).1 = -signedWeight weight F.1 := by
  rcases F with ⟨F, hF⟩
  cases F with
  | good _ => contradiction
  | bad B =>
      simp [badTailSwapEquiv, badTailSwap, signedWeight, perm, unsignedWeight,
        LGVBadFamily.sign_tailSwap, LGVBadFamily.unsignedWeight_tailSwap]

end LGVFamily

/--
The concrete LGV bad-involution certificate obtained from the marked
Lindström tail-swap construction.
-/
def latticeLGVCertificate {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]
    (weight : V → R) : BadInvolutionCertificate (LGVFamily n V) R where
  bad := LGVFamily.isBad
  bad_decidable := inferInstance
  tauBad := LGVFamily.badTailSwapEquiv
  signedWeight := LGVFamily.signedWeight weight
  sign_reverse := LGVFamily.signedWeight_badTailSwap weight

/--
A finite path-count system for the determinant side of LGV.  `Path i j` is
the finite type of paths from source `i` to sink `j`, and `familyEquiv`
identifies the determinant expansion data `(σ, one path for each column i from
σ i to i)` with the concrete `LGVFamily` type used by the tail-swap
certificate.
-/
structure PathCountSystem (n : ℕ) (V R : Type*) [DecidableEq V] [CommRing R] where
  vertexWeight : V → R
  Path : Fin n → Fin n → Type*
  pathFintype : ∀ i j : Fin n, Fintype (Path i j)
  pathWeight : ∀ {i j : Fin n}, Path i j → R
  familyEquiv :
    (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, Path (σ i) i) ≃ LGVFamily n V
  weight_eq :
    ∀ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, Path (σ i) i),
      LGVFamily.signedWeight vertexWeight (familyEquiv X) =
        Equiv.Perm.sign X.1 • ∏ i : Fin n, pathWeight (X.2 i)

namespace PathCountSystem

variable {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]

/-- The weighted path-count matrix entry. -/
def pathCount (S : PathCountSystem n V R) (i j : Fin n) : R :=
  letI := S.pathFintype i j
  ∑ p : S.Path i j, S.pathWeight p

/-- The LGV path-count matrix. -/
def matrix (S : PathCountSystem n V R) : Matrix (Fin n) (Fin n) R :=
  fun i j => S.pathCount i j



end PathCountSystem







/-
Tiny compiled application of `chapter30`.

The current `PathCountSystem` still targets `LGVFamily n V`, whose paths are
unbounded `List V`s.  For a nonempty geometric vertex type this is not a finite
type without an additional bounded/geometric path layer, so full grid-path
applications such as the hook-length formula still require more infrastructure.
The empty-vertex case below is the smallest finite instance: there is one formal
path in every entry of a `2 × 2` path-count matrix, and the two signed
non-intersecting families cancel.
-/
namespace EmptyTwoByTwoExample



def emptyGoodFamily (σ : Equiv.Perm (Fin 2)) : LGVFamily 2 Empty :=
  LGVFamily.good
    { perm := σ
      paths := fun _ => []
      nonIntersecting := by
        intro _ _ _
        simp }

def emptyFamilyPerm : LGVFamily 2 Empty → Equiv.Perm (Fin 2)
  | LGVFamily.good G => G.perm
  | LGVFamily.bad B => Empty.elim B.shared

theorem emptyGoodFamily_emptyFamilyPerm (F : LGVFamily 2 Empty) :
    emptyGoodFamily (emptyFamilyPerm F) = F := by
  cases F with
  | good G =>
      cases G with
      | mk perm paths nonIntersecting =>
          dsimp [emptyGoodFamily, emptyFamilyPerm]
          have hpaths : paths = fun _ : Fin 2 => ([] : List Empty) := by
            funext i
            cases paths i with
            | nil => rfl
            | cons head _ => cases head
          cases hpaths
          rfl
  | bad B =>
      cases B.shared

def emptyFamilyEquiv : LGVFamily 2 Empty ≃ Equiv.Perm (Fin 2) where
  toFun := emptyFamilyPerm
  invFun := emptyGoodFamily
  left_inv := emptyGoodFamily_emptyFamilyPerm
  right_inv := by intro _; rfl

noncomputable instance instFintypeLGVFamilyEmptyTwo : Fintype (LGVFamily 2 Empty) :=
  Fintype.ofEquiv (Equiv.Perm (Fin 2)) emptyFamilyEquiv.symm

noncomputable instance instDecidableEqLGVFamilyEmptyTwo : DecidableEq (LGVFamily 2 Empty) :=
  Equiv.decidableEq emptyFamilyEquiv













end EmptyTwoByTwoExample

end ProofsInTheBook.Chapter30


