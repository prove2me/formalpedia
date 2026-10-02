-- Prove2me | Definitions.Def_P2MAssembly_Chapter39
-- name    : P2MAssembly_Chapter39
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T17:02:59.609811+00:00
-- url     : https://prove2.me/theorems/f6f2a642-3906-4812-93cb-97c4a5542f48
-- title:
--   Kneser graphs, signed-subset chains, and alternating-deletion incidence
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). For $n,k\in\mathbb N$, the vertices of $KG(n,k)$ are the $k$-subsets of $[n]$; adjacency means distinctness and disjointness. A coloring assigns a finite color index to each vertex, and the minimum color on a support is the minimum among its contained $k$-subsets. A signed subset of $[n]$ is a pair $(P,N)$ of disjoint subsets, nonzero when $P\cup N\ne\varnothing$; its antipode is $(N,P)$ and its partial order is componentwise inclusion. A signed label is a sign paired with an index, and label negation reverses the sign. A signed permutation gives an ordering and a sign for each position; its successive prefixes form a maximal chain of nonzero signed subsets. The upper hemisphere consists of signed subsets whose negative part omits the last coordinate, and the equator omits that coordinate from both parts.
--
--   For a sequence $M:[\ell]\to\{+,-\}\times[m]$, write $\operatorname{Alt}_+(M)$ when there exists a strictly increasing $u:[\ell]\to[m]$ such that $\operatorname{im}M=\{((-1)^a,u(a)):a\in[\ell]\}$, and define $\operatorname{Alt}_-(M)$ by reversing all these signs. Here $(-1)^a$ denotes the positive sign for even $a$. These predicates concern the label set ordered by index, not the input order. For a sign sequence $s:[k+1]\to\{+1,-1\}$, a deletion position $i$ satisfies $s_j=(-1)^j$ before $i$ and $s_j=-(-1)^j$ after $i$. For an index map $u:[r]\to[m]$, the indexed target label set is $A_u=\{((-1)^j,u(j)):j\in[r]\}$; a target-set deletion is a position whose removal leaves every target label represented. The standard target uses $u(j)=j$.
--
--   The bundle also defines actual upper-hemisphere ridges as ordered chains obtained by deleting one rank of a signed-permutation prefix chain, with prescribed or alternating retained labels. Incidence with a maximal chain means equality with such a deletion; a boundary ridge lies entirely on the equator. The associated finite degree-data structure consists of finite sets $R,S$, a decidable relation $E\subseteq R\times S$, a decidable boundary predicate $B\subseteq R$, a witness $R\ne\varnothing$, and the required equalities
--   $$|\{s\in S:E(r,s)\}|=\begin{cases}1&r\in B,\\2&r\notin B\end{cases}\qquad(r\in R).$$
--   Tucker and Ky Fan predicates quantify over antipodal labelings, with the relevant no-complementary-comparable-label condition and alternating-chain counts. Equator restrictions, embeddings, chain transports, and finite incidence equivalences connect these objects. These are definitions and data requirements; the degree equalities in the structure are inputs to that structure.
-- source:
--   Original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39.lean#L44 (Kneser vertices), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39.lean#L330 (signed subsets), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39.lean#L493 (signed labels), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39.lean#L1114 (signed permutations); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L625 (sign-sequence deletions), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L1040 (alternating label sequences), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L2369 (degree data), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L4696 (actual alternating ridges). Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter39 -/
section
set_option autoImplicit true


/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and formalizes Matoušek's finite reduction from a too-small Kneser
coloring to a Tucker-labeling counterexample.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The remaining upstream gap is now the finite Ky Fan boundary-parity count,
formalized in two equivalent ways: `KyFanPrefixParityStatement` says that the
positive-first alternating signed-permutation prefix chains are odd, while
`KyFanPrefixModFourStatement` says that both orientations together have
cardinality `2 mod 4`.  This file proves the Matoušek construction from a
hypothetical `(n - 2*k + 1)`-coloring of `KG(n,k)` to a Tucker counterexample,
proves low-dimensional Tucker cases, packages them into an unconditional
low-dimensional Lovász theorem, proves the one-dimensional Ky Fan prefix-parity
count and the vacuous two-dimensional Ky Fan prefix-parity case, and proves
either Ky Fan parity frontier implies
`TuckerLemmaStatement → chapter39`.
-/

namespace ProofsInTheBook.Chapter39

/-- Vertices of the Kneser graph `KG(n,k)`: the `k`-subsets of `[n]`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance (n k : ℕ) : Fintype (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

instance (n k : ℕ) : DecidableEq (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

/-- The Kneser graph: vertices are `k`-subsets, adjacent when disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj a b := a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩



































/--
The minimum element of a k-subset (well-defined since k ≥ 1).
-/
noncomputable def KneserVertex.min' {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : Fin n :=
  S.1.min' (by rw [Finset.nonempty_iff_ne_empty]; intro h; have := S.2; simp [h] at this; omega)

/--
The Kneser coloring by minimum element: color each k-subset by its minimum
when that minimum is ≤ n-2k, otherwise assign the default color n-2k+1.
-/
noncomputable def kneserColorNat {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : ℕ :=
  let m := (KneserVertex.min' hk S).val
  if m ≤ n - 2 * k then m else n - 2 * k + 1

theorem kneserColorNat_lt {n k : ℕ} (_hk : 1 ≤ k) (_h2k : 2 * k ≤ n)
    (S : KneserVertex n k) : kneserColorNat _hk S < n - 2 * k + 2 := by
  unfold kneserColorNat
  simp only
  by_cases h : (KneserVertex.min' _hk S).val ≤ n - 2 * k
  · simp [h]
    omega
  · simp [h]

noncomputable def kneserColor {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    KneserVertex n k → Fin (n - 2 * k + 2) :=
  fun S => ⟨kneserColorNat hk S, kneserColorNat_lt hk h2k S⟩





/-! ### Tucker-lemma route for the hard lower bound -/

/-- A sign vector in `{−1,0,1}^n`, represented by its positive and negative supports. -/
structure SignedSubset (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  disjoint : Disjoint pos neg

namespace SignedSubset

/-- Antipodal sign vector: swap positive and negative supports. -/
def antipode {n : ℕ} (X : SignedSubset n) : SignedSubset n where
  pos := X.neg
  neg := X.pos
  disjoint := X.disjoint.symm

/-- The sign vector is not the origin. -/
def Nonzero {n : ℕ} (X : SignedSubset n) : Prop :=
  X.pos.Nonempty ∨ X.neg.Nonempty

theorem antipode_nonzero {n : ℕ} (X : SignedSubset n) :
    X.antipode.Nonzero ↔ X.Nonzero := by
  simp [Nonzero, antipode, or_comm]

/-- Total support size of a sign vector. -/
def card {n : ℕ} (X : SignedSubset n) : ℕ :=
  X.pos.card + X.neg.card



theorem card_pos_of_nonzero {n : ℕ} {X : SignedSubset n} (hX : X.Nonzero) :
    0 < X.card := by
  rcases hX with hpos | hneg
  · simp [card, Finset.card_pos.2 hpos]
  · simp [card, Finset.card_pos.2 hneg]

/-- The unsigned support of a sign vector. -/
def support {n : ℕ} (X : SignedSubset n) : Finset (Fin n) :=
  X.pos ∪ X.neg



theorem support_nonempty_iff_nonzero {n : ℕ} (X : SignedSubset n) :
    X.support.Nonempty ↔ X.Nonzero := by
  simp [support, Nonzero]

/-- The largest coordinate in the support of a nonzero sign vector. -/
noncomputable def maxSupport {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Fin n :=
  X.support.max' ((support_nonempty_iff_nonzero X).mpr hX)







/-- The sign of the largest supported coordinate, used in Matoušek's small-support labels. -/
noncomputable def maxSupportPositive {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Bool :=
  decide (X.maxSupport hX ∈ X.pos)





/-- The face order on the cross-polytope boundary, by support inclusion. -/
def Le {n : ℕ} (X Y : SignedSubset n) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

/-- Select the positive or negative support of a sign vector. -/
def side {n : ℕ} (X : SignedSubset n) (positive : Bool) : Finset (Fin n) :=
  if positive then X.pos else X.neg

@[simp]
theorem side_true {n : ℕ} (X : SignedSubset n) : X.side true = X.pos := by
  simp [side]

@[simp]
theorem side_false {n : ℕ} (X : SignedSubset n) : X.side false = X.neg := by
  simp [side]







end SignedSubset

/-- Nonzero sign vectors, i.e. vertices/faces of the deleted origin sign complex. -/
abbrev NonzeroSignedSubset (n : ℕ) :=
  {X : SignedSubset n // X.Nonzero}

namespace NonzeroSignedSubset

/-- Antipodal map on nonzero sign vectors. -/
def antipode {n : ℕ} (X : NonzeroSignedSubset n) : NonzeroSignedSubset n :=
  ⟨X.1.antipode, (SignedSubset.antipode_nonzero X.1).mpr X.2⟩

end NonzeroSignedSubset

/-- A signed label `±i`, with `i : Fin m`. -/
structure SignedLabel (m : ℕ) where
  positive : Bool
  index : Fin m
  deriving DecidableEq, Repr

namespace SignedLabel

/-- Negating a signed label flips its sign and keeps its index. -/
def neg {m : ℕ} (L : SignedLabel m) : SignedLabel m where
  positive := !L.positive
  index := L.index

theorem ext {m : ℕ} {L M : SignedLabel m}
    (hpositive : L.positive = M.positive) (hindex : L.index = M.index) : L = M := by
  cases L
  cases M
  simp at hpositive hindex
  subst hpositive
  subst hindex
  rfl

end SignedLabel

/-- `k`-subsets contained in a fixed finite support. -/
abbrev KneserVertexIn (n k : ℕ) (support : Finset (Fin n)) : Type :=
  {A : KneserVertex n k // (A.1 : Finset (Fin n)) ⊆ support}

instance (n k : ℕ) (support : Finset (Fin n)) :
    Fintype (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

instance (n k : ℕ) (support : Finset (Fin n)) :
    DecidableEq (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

theorem KneserVertexIn.nonempty_of_le_card {n k : ℕ} {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    Nonempty (KneserVertexIn n k support) := by
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨⟨⟨A, hAcard⟩, hAsub⟩⟩

/-- The set of colors used on `k`-subsets contained in a support. -/
noncomputable def colorsInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) : Finset (Fin q) :=
  Finset.univ.image fun A : KneserVertexIn n k support => C A.1

theorem colorsInSupport_nonempty {n k q : ℕ} (C : KneserVertex n k → Fin q)
    {support : Finset (Fin n)} (hcard : k ≤ support.card) :
    (colorsInSupport C support).Nonempty := by
  classical
  obtain ⟨A⟩ := KneserVertexIn.nonempty_of_le_card (n := n) (k := k) hcard
  exact ⟨C A.1, by simp [colorsInSupport]⟩

/-- The minimum color appearing on a `k`-subset contained in `support`. -/
noncomputable def minColorInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) (hcard : k ≤ support.card) : Fin q :=
  (colorsInSupport C support).min' (colorsInSupport_nonempty C hcard)



@[simp]
theorem minColorInSupport_congr_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (support : Finset (Fin n))
    (h₁ h₂ : k ≤ support.card) :
    minColorInSupport C support h₁ = minColorInSupport C support h₂ := by
  unfold minColorInSupport
  congr



/--
Small-support part of Matoušek's labeling: a nonzero sign vector with total
support at most `2k - 2` receives label index `|X| - 1`.
-/
def matousekSmallSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    Fin (n - 1) :=
  ⟨X.card - 1, by
    have hpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
    omega⟩

/-- Full small-support signed label in Matoušek's construction. -/
noncomputable def matousekSmallSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    SignedLabel (n - 1) where
  positive := X.maxSupportPositive hX
  index := matousekSmallSupportIndex hk hn X hX hsmall









/--
Large-support color labels occupy the range `2k - 2, …, n - 2`, obtained by
adding the color value to the offset `2k - 2`.
-/
def matousekLargeSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (color : Fin (n - 2 * k + 1)) : Fin (n - 1) :=
  ⟨2 * k - 2 + color.val, by
    have hcolor := color.isLt
    omega⟩

/-- If a sign vector has support at least `2k - 1`, then one side has a `k`-subset. -/
theorem signedSubset_large_support_has_k_side {n k : ℕ} {X : SignedSubset n}
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ X.pos.card ∨ k ≤ X.neg.card := by
  by_contra h
  push Not at h
  simp [SignedSubset.card] at hlarge
  omega



/--
Large-support side choice in Matoušek's construction: use the side whose
contained `k`-subsets have smaller minimum color, breaking one-sided cases by
choosing the only side that contains a `k`-subset.
-/
noncomputable def matousekLargeSupportPositive {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (_hlarge : 2 * k - 1 ≤ X.card) : Bool :=
  if hpos : k ≤ X.pos.card then
    if hneg : k ≤ X.neg.card then
      decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg)
    else true
  else false



theorem matousekLargeSupportPositive_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ (X.side (matousekLargeSupportPositive C X hlarge)).card := by
  unfold matousekLargeSupportPositive
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · by_cases hlt : minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg
      · simp [hpos, hneg, hlt]
      · simp [hpos, hneg, hlt]
    · simp [hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [hpos, hneg]



/-- The minimum color on the selected large-support side. -/
noncomputable def matousekLargeSupportColor {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : Fin q :=
  minColorInSupport C (X.side (matousekLargeSupportPositive C X hlarge))
    (matousekLargeSupportPositive_card C X hlarge)





/-- Full large-support signed label in Matoušek's construction. -/
noncomputable def matousekLargeSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : SignedLabel (n - 1) where
  positive := matousekLargeSupportPositive C X hlarge
  index := matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge)













/-- Matoušek's sign-vector label produced by a hypothetical too-small coloring. -/
noncomputable def matousekTuckerLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) :
    NonzeroSignedSubset n → SignedLabel (n - 1) :=
  fun X =>
    if hsmall : X.1.card ≤ 2 * k - 2 then
      matousekSmallSupportLabel hk hn X.1 X.2 hsmall
    else
      matousekLargeSupportLabel hk hn C X.1 (by omega)





/--
Tucker's lemma in the octahedral/sign-vector form needed for the Matoušek
proof of Lovász's theorem.  The remaining proof obligation is supplied by the
finer `KyFanPrefixParityStatement` below.
-/
def TuckerLemmaStatement (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, label X.antipode = (label X).neg) →
      ∃ X Y : NonzeroSignedSubset n,
        SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg





/-- A sign-vector labeling has no complementary comparable pair. -/
def NoComplementaryComparableLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Prop :=
  ∀ X Y : NonzeroSignedSubset n,
    SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg











/--
A signed permutation, i.e. a maximal chain in the face lattice of the
cross-polytope boundary: reveal the coordinates in `order`, with the prescribed
sign at each coordinate.
-/
structure SignedPermutation (n : ℕ) where
  order : Equiv.Perm (Fin n)
  positive : Fin n → Bool
  deriving DecidableEq

def signedPermutationEquiv (n : ℕ) :
    SignedPermutation n ≃ Equiv.Perm (Fin n) × (Fin n → Bool) where
  toFun P := (P.order, P.positive)
  invFun data := { order := data.1, positive := data.2 }
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro data
    cases data
    rfl

noncomputable instance (n : ℕ) : Fintype (SignedPermutation n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n) × (Fin n → Bool)) (signedPermutationEquiv n).symm

namespace SignedPermutation

/-- Antipodal signed permutation: keep the order and flip every sign. -/
def antipode {n : ℕ} (P : SignedPermutation n) : SignedPermutation n where
  order := P.order
  positive := fun i => !P.positive i

theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro P
  cases P
  simp [antipode]



/-- Positive coordinates in the `i`th prefix face of a signed permutation. -/
def prefixPos {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ P.positive (P.order.symm x)

/-- Negative coordinates in the `i`th prefix face of a signed permutation. -/
def prefixNeg {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ !P.positive (P.order.symm x)

theorem prefix_disjoint {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    Disjoint (P.prefixPos i) (P.prefixNeg i) := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  simp [prefixPos, prefixNeg] at hxpos hxneg
  cases h : P.positive (P.order.symm x) <;> simp [h] at hxpos hxneg





/-- The `i`th prefix face as a sign vector. -/
def prefixSignedSubset {n : ℕ} (P : SignedPermutation n) (i : Fin n) : SignedSubset n where
  pos := P.prefixPos i
  neg := P.prefixNeg i
  disjoint := P.prefix_disjoint i

theorem prefix_nonzero {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).Nonzero := by
  let x : Fin n := P.order i
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hsymm : P.order.symm x = i := by simp [x]
  have hle : P.order.symm x ≤ i := le_of_eq hsymm
  by_cases hpos : P.positive (P.order.symm x) = true
  · left
    exact ⟨x, by simp [prefixSignedSubset, prefixPos, hxuniv, hle, hpos]⟩
  · right
    exact ⟨x, by simp [prefixSignedSubset, prefixNeg, hxuniv, hle, hpos]⟩

/-- The maximal chain associated to a signed permutation. -/
def prefixChain {n : ℕ} (P : SignedPermutation n) (i : Fin n) : NonzeroSignedSubset n :=
  ⟨P.prefixSignedSubset i, P.prefix_nonzero i⟩

theorem prefixSignedSubset_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixSignedSubset i = (P.prefixSignedSubset i).antipode := by
  cases P with
  | mk order positive =>
      simp [antipode, prefixSignedSubset, prefixPos, prefixNeg, SignedSubset.antipode]

theorem prefixChain_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixChain i = (P.prefixChain i).antipode := by
  apply Subtype.ext
  exact P.prefixSignedSubset_antipode i





end SignedPermutation













/--
Positive-first alternating prefix labels: the absolute label indices strictly
increase, and the signs alternate `+,-,+,-,...` along the prefix chain.
-/
def PositiveAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = decide (Even i.val)

/-- Negative-first alternating prefix labels, the antipodal partner of the positive-first version. -/
def NegativeAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = !decide (Even i.val)





/-- Signed permutations whose prefix labels are positive-first alternating. -/
noncomputable def positiveAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => PositiveAlternatingPrefixLabels label P

/-- Signed permutations whose prefix labels are negative-first alternating. -/
noncomputable def negativeAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => NegativeAlternatingPrefixLabels label P





/-- Positive- or negative-first alternating prefix-label chains. -/
noncomputable def alternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  positiveAlternatingPrefixLabelChains label ∪ negativeAlternatingPrefixLabelChains label























/-! ### Endpoint-count form of the remaining Ky Fan parity frontier -/



















namespace PathEndpointDecomposition



end PathEndpointDecomposition



































/--
Matoušek's bridge from a too-small Kneser coloring to a Tucker counterexample:
given a proper `(n - 2*k + 1)`-coloring, construct an antipodal sign-vector
labeling with no complementary comparable pair.
-/
def KneserColoringProducesTuckerCounterexample (n k : ℕ) : Prop :=
  ∀ C : KneserVertex n k → Fin (n - 2 * k + 1),
    (∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) →
      ∃ label : NonzeroSignedSubset n → SignedLabel (n - 1),
        (∀ X, label X.antipode = (label X).neg) ∧
          ∀ X Y : NonzeroSignedSubset n,
            SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg































end ProofsInTheBook.Chapter39

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter39
import Mathlib.Data.Fin.Tuple.Sort
-/
/- Source module: ProofsInTheBook.Chapter39Tucker -/
section
set_option autoImplicit true


/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation







/-! ## Hemisphere and equator model -/

theorem signedSubset_ext_pos_neg {n : ℕ} {X Y : SignedSubset n}
    (hpos : X.pos = Y.pos) (hneg : X.neg = Y.neg) : X = Y := by
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

/-- The upper hemisphere `B⁺_{r+1}`: the last coordinate is not negative. -/
def UpperHemisphere {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.neg

/-- The equator of `B⁺_{r+1}`: the last coordinate is zero. -/
def Equator {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.pos ∧ Fin.last r ∉ X.1.neg

theorem equator_subset_upperHemisphere {r : ℕ} {X : NonzeroSignedSubset (r + 1)}
    (hX : Equator X) : UpperHemisphere X :=
  hX.2

theorem upperHemisphere_of_le {r : ℕ} {X Y : NonzeroSignedSubset (r + 1)}
    (hXY : SignedSubset.Le X.1 Y.1) (hY : UpperHemisphere Y) :
    UpperHemisphere X := by
  intro hneg
  exact hY (hXY.2 hneg)

/-- Embed a sign vector on the first `r` coordinates into the equator of
`{−1,0,1}^{r+1}`. -/
def signedSubsetEquatorEmbed {r : ℕ} (X : SignedSubset r) : SignedSubset (r + 1) where
  pos := X.pos.image Fin.castSucc
  neg := X.neg.image Fin.castSucc
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hypos hyneg
    rcases Finset.mem_image.mp hypos with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hyneg with ⟨b, hbmem, hb⟩
    have hba : b = a := by
      apply Fin.ext
      simpa using congrArg Fin.val hb
    subst b
    exact (Finset.disjoint_left.mp X.disjoint) ha hbmem

/-- The equator embedding on nonzero sign vectors. -/
def equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) : NonzeroSignedSubset (r + 1) :=
  ⟨signedSubsetEquatorEmbed X.1, by
    rcases X.2 with hpos | hneg
    · rcases hpos with ⟨i, hi⟩
      left
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩
    · rcases hneg with ⟨i, hi⟩
      right
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩⟩

theorem equatorEmbed_mem_equator {r : ℕ} (X : NonzeroSignedSubset r) :
    Equator (equatorEmbed X) := by
  constructor
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega

/-- The predecessor of a non-last coordinate. -/
def finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) : Fin r :=
  ⟨i.val, by
    have hle : i.val ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hne : i.val ≠ r := by
      intro hval
      exact hi (Fin.ext hval)
    omega⟩

@[simp]
theorem castSucc_finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) :
    Fin.castSucc (finPredOfNotLast i hi) = i := by
  apply Fin.ext
  rfl

/-- Drop the last zero coordinate from an equatorial sign vector. -/
def equatorDropSignedSubset {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : SignedSubset r where
  pos := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.pos
  neg := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.neg
  disjoint := by
    rw [Finset.disjoint_left]
    intro i hip hin
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hip hin
    exact (Finset.disjoint_left.mp X.1.disjoint) hip hin

theorem equatorDrop_nonzero {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) : (equatorDropSignedSubset X).Nonzero := by
  rcases X.2 with hpos | hneg
  · rcases hpos with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.1 (by simpa [hlast] using hi)
    left
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩
  · rcases hneg with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.2 (by simpa [hlast] using hi)
    right
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩

/-- The inverse map from the equator back to `K_r`. -/
def equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1)) (hX : Equator X) :
    NonzeroSignedSubset r :=
  ⟨equatorDropSignedSubset X, equatorDrop_nonzero X hX⟩

theorem equatorDrop_equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorDrop (equatorEmbed X) (equatorEmbed_mem_equator X) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]

theorem equatorEmbed_equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) :
    equatorEmbed (equatorDrop X hX) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.1 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.2 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast

/-- The equator of the upper hemisphere in `K_{r+1}` is canonically `K_r`. -/
noncomputable def equatorEquiv (r : ℕ) :
    NonzeroSignedSubset r ≃ {X : NonzeroSignedSubset (r + 1) // Equator X} where
  toFun X := ⟨equatorEmbed X, equatorEmbed_mem_equator X⟩
  invFun X := equatorDrop X.1 X.2
  left_inv := by
    intro X
    exact equatorDrop_equatorEmbed X
  right_inv := by
    intro X
    cases X with
    | mk X hX =>
        apply Subtype.ext
        exact equatorEmbed_equatorDrop X hX







noncomputable def equatorRestrictedLabel {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    NonzeroSignedSubset d → SignedLabel d :=
  fun X => label ((equatorEquiv d) X).1

noncomputable def equatorRestrictedLabelOf {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    NonzeroSignedSubset r → SignedLabel m :=
  fun X => label ((equatorEquiv r) X).1

















/-! ## Label-set `A` ridges and the local sigma-degree count -/

/-- The alternating label `α_k = (-1)^k(k+1)` in zero-based `Fin d` notation. -/
def alternatingLabel (k : Fin d) : SignedLabel d where
  positive := decide (Even k.val)
  index := k











/-- The concrete `A = {+1,-2,+3,...}` label set. -/
noncomputable def alternatingLabelSetA (d : ℕ) : Finset (SignedLabel d) :=
  Finset.univ.image fun k : Fin d => alternatingLabel k



/-! ### Alternating labels along an arbitrary increasing index set -/

/-- The alternating label attached to the `a`th element of an index map.  The
sign alternates with the position `a`; the absolute label is `idx a`. -/
def alternatingLabelOf {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    SignedLabel m where
  positive := decide (Even a.val)
  index := idx a





theorem alternatingLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    alternatingLabelOf idx a = alternatingLabelOf idx b ↔ a = b := by
  constructor
  · intro h
    apply hidx
    simpa [alternatingLabelOf] using congrArg SignedLabel.index h
  · intro h
    subst h
    rfl



/-- The alternating label set determined by an index map. -/
noncomputable def alternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => alternatingLabelOf idx a

theorem alternatingLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingLabelSetOf idx).card = r := by
  classical
  rw [alternatingLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingLabelOf_inj hidx).mp h

/-- The negative-first alternating label set determined by an index map. -/
noncomputable def alternatingNegLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => (alternatingLabelOf idx a).neg













/-- The label set carried by an ordered simplex.  The property below does not
use the order except to enumerate the finitely many vertices. -/
noncomputable def simplexLabelSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin k => label (sigma a)

/-- Positive-first alternating simplex, with its index set read off from the
simplex itself.  The `idx` below is an internal witness, not an external
summation parameter. -/
def IsAltPos {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingLabelSetOf idx

/-- Negative-first alternating simplex, with the same self-contained indexing
convention as `IsAltPos`. -/
def IsAltNeg {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingNegLabelSetOf idx

noncomputable instance isAltPos_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltPos label sigma) := by
  classical
  unfold IsAltPos
  infer_instance

noncomputable instance isAltNeg_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltNeg label sigma) := by
  classical
  unfold IsAltNeg
  infer_instance





/-! ### Pure sign-sequence deletion parity -/

def signSeqAltPos {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = decide (Even i.val)

def signSeqAltNeg {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = !decide (Even i.val)

def signSeqDoor {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  (∀ j : Fin (k + 1), j < i → s j = decide (Even j.val)) ∧
    (∀ j : Fin (k + 1), i < j → s j = !decide (Even j.val))

noncomputable def signSeqDoorSet {k : ℕ} (s : Fin (k + 1) → Bool) :
    Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter (signSeqDoor s)

noncomputable instance signSeqDoor_decidable {k : ℕ} (s : Fin (k + 1) → Bool) :
    DecidablePred (signSeqDoor s) := by
  classical
  exact inferInstance

def signSeqBad {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  s i = !decide (Even i.val)





























/-! ### Sorted label-sequence deletion parity -/

noncomputable def labelSeqSet {k m : ℕ} (L : Fin k → SignedLabel m) :
    Finset (SignedLabel m) :=
  Finset.univ.image L

def IsAltPosLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingLabelSetOf idx

def IsAltNegLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingNegLabelSetOf idx

noncomputable instance isAltPosLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltPosLabelSeq L) := by
  classical
  unfold IsAltPosLabelSeq
  infer_instance

noncomputable instance isAltNegLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltNegLabelSeq L) := by
  classical
  unfold IsAltNegLabelSeq
  infer_instance



theorem sortedLabelSeq_isAltNeg_iff_signSeqAltNeg {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltNegLabelSeq L ↔ signSeqAltNeg sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingNegLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : (alternatingLabelOf eta b).neg ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingNegLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingNegLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]

noncomputable def labelSeqAltPosDeletionSet {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun j => IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a))









noncomputable def simplexAltPosDeletionSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin (k + 1) → NonzeroSignedSubset n) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun j => IsAltPos label (fun a : Fin k => sigma (j.succAbove a))























def NoOppositeLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∀ i j : Fin k, L i ≠ (L j).neg







/-! ## Ky Fan parity statement on the non-degenerate range -/

/-- Ky Fan parity in the range actually used by Tucker: `r ≥ 1`, `m ≥ r`.
It counts positive-first alternating maximal chains of `K_r`; this is not the
degenerate `Fin r → Fin (r-1)` full-chain pigeonhole setup. -/
def KyFanParityStatement (r m : ℕ) : Prop :=
  1 ≤ r →
    r ≤ m →
      ∀ label : NonzeroSignedSubset r → SignedLabel m,
        (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
            Odd (positiveAlternatingPrefixLabelChains label).card









/-- After deleting `j` from a `(d+1)`-vertex sigma, every label in `A` still
appears.  Since exactly `d` vertices remain, this is the label-set-`A` door
condition used in the deletion count. -/
def SigmaDeletionHasAlternatingLabelSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) (j : Fin (d + 1)) : Prop :=
  ∀ a : Fin d, ∃ t : Fin (d + 1), t ≠ j ∧ sigmaLabel t = alternatingLabel a

/-- The door set of a sigma: deletions that leave the alternating label set `A`. -/
noncomputable def sigmaDoorSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) : Finset (Fin (d + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSet sigmaLabel j

/-- The parameterized deletion condition: deleting `j` leaves the alternating
label set determined by `idx`. -/
def SigmaDeletionHasAlternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) (j : Fin (r + 1)) : Prop :=
  ∀ a : Fin r, ∃ t : Fin (r + 1), t ≠ j ∧
    sigmaLabel t = alternatingLabelOf idx a

/-- Door set for a fixed increasing index set. -/
noncomputable def sigmaDoorSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) : Finset (Fin (r + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j





























































/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/









/-- A checked, non-degenerate package for the codimension-one rho degree in
the upper hemisphere.  `R` is the finite type of actual `(r-2)`-ridges and `S`
the finite type of upper top simplices incident to them; `nonempty_R` records
that the ridge side has not collapsed to an empty type. -/
structure RhoDegreeManifoldData (R S : Type*) [Fintype R] [Fintype S] where
  edge : R → S → Prop
  edge_decidable : DecidableRel edge
  boundary : R → Prop
  boundary_decidable : DecidablePred boundary
  nonempty_R : Nonempty R
  degree_card :
    ∀ r : R,
      Fintype.card {s : S // edge r s} = if boundary r then 1 else 2

namespace RhoDegreeManifoldData

attribute [instance] edge_decidable boundary_decidable





end RhoDegreeManifoldData





























namespace SignedPermutation

theorem ext_order_positive {n : ℕ} {P Q : SignedPermutation n}
    (horder : P.order = Q.order) (hpositive : P.positive = Q.positive) : P = Q := by
  cases P
  cases Q
  simp at horder hpositive
  subst horder
  subst hpositive
  rfl

/-- Reindex the positions of a signed permutation, moving the signed atoms
together.  For adjacent swaps this is the second top simplex through a
punctured full flag. -/
def reindexPositions {n : ℕ} (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) :
    SignedPermutation n where
  order := τ.trans P.order
  positive := fun i => P.positive (τ i)





theorem reindexPositions_swap_ne_self {n : ℕ}
    (P : SignedPermutation n) {a b : Fin n} (hab : a ≠ b) :
    P.reindexPositions (Equiv.swap a b) ≠ P := by
  intro h
  have horder := congrArg SignedPermutation.order h
  have hfun := congrArg (fun e : Equiv.Perm (Fin n) => e a) horder
  simp [reindexPositions] at hfun
  exact hab hfun.symm

/-- The successor of a non-last deleted rank, as an element of the same `Fin`
type. -/
def gapNext {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) : Fin (n + 1) :=
  ⟨gap.val + 1, by omega⟩

theorem gapNext_val {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (gapNext gap hgap).val = gap.val + 1 :=
  rfl

theorem reindexPositions_swap_gap_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    P.reindexPositions (Equiv.swap gap (gapNext gap hgap)) ≠ P := by
  apply P.reindexPositions_swap_ne_self
  intro h
  have hval := congrArg Fin.val h
  simp [gapNext] at hval

/-- Flip the sign introduced at one position, keeping the order fixed. -/
def flipSignAt {n : ℕ} (P : SignedPermutation n) (j : Fin n) : SignedPermutation n where
  order := P.order
  positive := fun i => if i = j then !P.positive i else P.positive i



theorem flipSignAt_ne_self {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    P.flipSignAt j ≠ P := by
  intro h
  have hpositive := congrArg SignedPermutation.positive h
  have hj := congrFun hpositive j
  cases hsign : P.positive j <;> simp [flipSignAt, hsign] at hj

theorem prefixSignedSubset_support {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).support =
      Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i := by
  ext x
  by_cases hpos : P.positive (P.order.symm x)
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]

theorem prefix_support_eq_order_image_Iic {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i) =
      (Finset.Iic i).map P.order.toEmbedding := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_map.mpr ⟨P.order.symm x, ?_, by simp⟩
    simpa using hx
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
    simpa using hj

theorem prefix_support_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i).card = i.val + 1 := by
  rw [prefix_support_eq_order_image_Iic P i, Finset.card_map]
  simp

theorem prefixSignedSubset_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).card = i.val + 1 := by
  have hsupport_card :
      (P.prefixSignedSubset i).support.card = (P.prefixSignedSubset i).card := by
    simp [SignedSubset.support, SignedSubset.card, prefixSignedSubset,
      Finset.card_union_of_disjoint (P.prefix_disjoint i)]
  rw [← hsupport_card, prefixSignedSubset_support, prefix_support_card]

theorem prefixChain_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixChain i).1.card = i.val + 1 :=
  P.prefixSignedSubset_card i

theorem prefixChain_card_lt_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    (P.prefixChain i).1.card < (P.prefixChain j).1.card := by
  rw [P.prefixChain_card i, P.prefixChain_card j]
  omega

theorem prefixChain_ne_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    P.prefixChain i ≠ P.prefixChain j := by
  intro h
  have hcard := congrArg (fun X : NonzeroSignedSubset n => X.1.card) h
  have hlt := P.prefixChain_card_lt_of_lt hij
  exact (ne_of_lt hlt) hcard

theorem prefixChain_injective {n : ℕ} (P : SignedPermutation n) :
    Function.Injective P.prefixChain := by
  intro i j hij
  by_cases h : i = j
  · exact h
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (P.prefixChain_ne_of_lt hlt hij).elim
    · exact (P.prefixChain_ne_of_lt hgt hij.symm).elim





theorem order_mem_prefixPos_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixPos j ↔ i ≤ j ∧ P.positive i := by
  simp [prefixPos]

theorem order_mem_prefixNeg_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixNeg j ↔ i ≤ j ∧ !P.positive i := by
  simp [prefixNeg]

theorem order_mem_prefix_support_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ (P.prefixSignedSubset j).support ↔ i ≤ j := by
  by_cases hpos : P.positive i
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]

theorem prefix_support_mem_order_iff {n : ℕ} (P : SignedPermutation n)
    (x : Fin n) (j : Fin n) :
    x ∈ (P.prefixSignedSubset j).support ↔ P.order.symm x ≤ j := by
  simpa using
    (order_mem_prefix_support_iff P (P.order.symm x) j :
      P.order (P.order.symm x) ∈ (P.prefixSignedSubset j).support ↔
        P.order.symm x ≤ j)

theorem order_positive_eq_of_prefixChain_eq_of_prev_eq {n : ℕ}
    (P Q : SignedPermutation n) (i : Fin n)
    (hcur : Q.prefixChain i = P.prefixChain i)
    (hprev :
      ∀ j : Fin n, j.val + 1 = i.val →
        Q.prefixChain j = P.prefixChain j) :
    Q.order i = P.order i ∧ Q.positive i = P.positive i := by
  let x : Fin n := Q.order i
  have hxQ : x ∈ (Q.prefixSignedSubset i).support := by
    simpa [x, prefixChain] using
      ((order_mem_prefix_support_iff Q i i).mpr le_rfl)
  have hsupport_cur :
      (Q.prefixSignedSubset i).support = (P.prefixSignedSubset i).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset n => X.1.support) hcur
  have hxP : x ∈ (P.prefixSignedSubset i).support := by
    simpa [hsupport_cur] using hxQ
  have hle : P.order.symm x ≤ i :=
    (prefix_support_mem_order_iff P x i).mp hxP
  have hnotlt : ¬ P.order.symm x < i := by
    intro hlt
    have hi_pos : 0 < i.val := by
      have hvlt := Fin.lt_iff_val_lt_val.mp hlt
      omega
    let ipred : Fin n := ⟨i.val - 1, by omega⟩
    have hipred_val : ipred.val + 1 = i.val := by
      dsimp [ipred]
      omega
    have hlePred : P.order.symm x ≤ ipred := by
      exact Fin.le_iff_val_le_val.mpr (by
        have hvlt := Fin.lt_iff_val_lt_val.mp hlt
        dsimp [ipred]
        omega)
    have hxPprev : x ∈ (P.prefixSignedSubset ipred).support :=
      (prefix_support_mem_order_iff P x ipred).mpr hlePred
    have hsupport_prev :
        (Q.prefixSignedSubset ipred).support =
          (P.prefixSignedSubset ipred).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.support)
          (hprev ipred hipred_val)
    have hxQprev : x ∈ (Q.prefixSignedSubset ipred).support := by
      simpa [hsupport_prev] using hxPprev
    have hqle : i ≤ ipred := by
      simpa [x] using (prefix_support_mem_order_iff Q x ipred).mp hxQprev
    have hvle := Fin.le_iff_val_le_val.mp hqle
    dsimp [ipred] at hvle
    omega
  have hsymm : P.order.symm x = i := le_antisymm hle (le_of_not_gt hnotlt)
  have horder : Q.order i = P.order i := by
    change x = P.order i
    simpa [x] using congrArg P.order hsymm
  have hsign : Q.positive i = P.positive i := by
    by_cases hqpos : Q.positive i
    · have hxQpos : x ∈ Q.prefixPos i := by
        simpa [x, order_mem_prefixPos_iff, hqpos]
      have hpos_cur : Q.prefixPos i = P.prefixPos i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hcur
      have hxPpos : P.order i ∈ P.prefixPos i := by
        simpa [x, horder, hpos_cur] using hxQpos
      have hppos : P.positive i := (order_mem_prefixPos_iff P i i).mp hxPpos |>.2
      simp [hqpos, hppos]
    · have hxQneg : x ∈ Q.prefixNeg i := by
        simpa [x, order_mem_prefixNeg_iff, hqpos]
      have hneg_cur : Q.prefixNeg i = P.prefixNeg i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hcur
      have hxPneg : P.order i ∈ P.prefixNeg i := by
        simpa [x, horder, hneg_cur] using hxQneg
      have hpneg : !P.positive i := (order_mem_prefixNeg_iff P i i).mp hxPneg |>.2
      cases hp : P.positive i <;> simp [hqpos, hp] at hpneg ⊢
  exact ⟨horder, hsign⟩

theorem positive_eq_of_order_eq_of_prefixChain_eq {n : ℕ}
    (P Q : SignedPermutation n) {i p j : Fin n}
    (horder : Q.order i = P.order p) (hij : i ≤ j) (hpj : p ≤ j)
    (hprefix : Q.prefixChain j = P.prefixChain j) :
    Q.positive i = P.positive p := by
  by_cases hqpos : Q.positive i
  · have hxQpos : Q.order i ∈ Q.prefixPos j := by
      simpa [order_mem_prefixPos_iff, hij, hqpos]
    have hpos_eq : Q.prefixPos j = P.prefixPos j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hprefix
    have hxPpos : P.order p ∈ P.prefixPos j := by
      simpa [horder, hpos_eq] using hxQpos
    have hppos : P.positive p := (order_mem_prefixPos_iff P p j).mp hxPpos |>.2
    simp [hqpos, hppos]
  · have hxQneg : Q.order i ∈ Q.prefixNeg j := by
      simpa [order_mem_prefixNeg_iff, hij, hqpos]
    have hneg_eq : Q.prefixNeg j = P.prefixNeg j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hprefix
    have hxPneg : P.order p ∈ P.prefixNeg j := by
      simpa [horder, hneg_eq] using hxQneg
    have hpneg : !P.positive p := (order_mem_prefixNeg_iff P p j).mp hxPneg |>.2
    cases hp : P.positive p <;> simp [hqpos, hp] at hpneg ⊢





theorem prefixSignedSubset_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixSignedSubset i = P.prefixSignedSubset i := by
  cases P with
  | mk order positive =>
      simp [prefixSignedSubset, prefixPos, prefixNeg, reindexPositions, hτ]

theorem prefixChain_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_reindexPositions_of_symm_le_iff τ i hτ

theorem swap_adjacent_symm_le_iff_of_ne_left {n : ℕ} {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    ∀ k : Fin n, (Equiv.swap a b).symm k ≤ i ↔ k ≤ i := by
  have habne : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  intro k
  by_cases hka : k = a
  · subst k
    have hswap : (Equiv.swap a b).symm a = b := by
      simp
    rw [hswap]
    constructor
    · intro h
      exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · intro h
      exact Fin.le_iff_val_le_val.mpr (by
        have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
        have hne : i.val ≠ a.val := by
          intro hval
          exact hi (Fin.ext hval)
        omega)
  · by_cases hkb : k = b
    · subst k
      have hswap : (Equiv.swap a b).symm b = a := by
        simp
      rw [hswap]
      constructor
      · intro h
        exact Fin.le_iff_val_le_val.mpr (by
          have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
          have hne : i.val ≠ a.val := by
            intro hval
            exact hi (Fin.ext hval)
          omega)
      · intro h
        exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · have hswap : (Equiv.swap a b).symm k = k := by
        simp [Equiv.swap_apply_def, hka, hkb]
      rw [hswap]

theorem prefixChain_reindexPositions_swap_adjacent_of_ne_left {n : ℕ}
    (P : SignedPermutation n) {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    (P.reindexPositions (Equiv.swap a b)).prefixChain i = P.prefixChain i :=
  P.prefixChain_reindexPositions_of_symm_le_iff (Equiv.swap a b) i
    (swap_adjacent_symm_le_iff_of_ne_left hab hi)

theorem prefixChain_reindexPositions_swap_gap_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (i : Fin n) :
    (P.reindexPositions (Equiv.swap gap (gapNext gap hgap))).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
  · exact gapNext_val gap hgap
  · exact Fin.succAbove_ne gap i

theorem prefixPos_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixPos i = P.prefixPos i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixPos, flipSignAt, hle, hne]
  · simp [prefixPos, flipSignAt, hle]

theorem prefixNeg_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixNeg i = P.prefixNeg i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixNeg, flipSignAt, hle, hne]
  · simp [prefixNeg, flipSignAt, hle]

theorem prefixSignedSubset_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixSignedSubset i = P.prefixSignedSubset i := by
  exact signedSubset_ext_pos_neg
    (P.prefixPos_flipSignAt_of_lt hij)
    (P.prefixNeg_flipSignAt_of_lt hij)

theorem prefixChain_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_flipSignAt_of_lt hij

theorem prefixChain_flipSignAt_last_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin n) :
    (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
      P.prefixChain ((Fin.last n).succAbove i) := by
  simpa [Fin.succAbove_last] using
    (P.prefixChain_flipSignAt_of_lt (j := Fin.last n) (Fin.castSucc_lt_last i))

end SignedPermutation

/-- Maximal chains lying in the upper hemisphere. -/
def UpperPrefixChain {n : ℕ} (P : SignedPermutation (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), UpperHemisphere (P.prefixChain i)

/-- A represented codimension-one ridge of the upper hemisphere is boundary
exactly when the deleted rank is the top rank and the last coordinate has not
appeared in the retained punctured flag. -/
def RepresentedUpperRidgeBoundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  gap = Fin.last n ∧ P.order.symm (Fin.last n) = Fin.last n

noncomputable instance representedUpperRidgeBoundary_decidable {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Decidable (RepresentedUpperRidgeBoundary P gap) := by
  classical
  exact inferInstance

/-- The second local top coface of a represented full-rank punctured flag in
the cross-polytope order complex: swap adjacent ranks when the missing rank is
internal, and flip the final inserted sign when the missing rank is top. -/
noncomputable def representedRidgePartner {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    SignedPermutation (n + 1) :=
  if hgap : gap.val < n then
    P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))
  else
    P.flipSignAt (Fin.last n)

theorem representedRidgePartner_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    representedRidgePartner P gap ≠ P := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap
  · simpa [hgap] using SignedPermutation.flipSignAt_ne_self P (Fin.last n)

theorem representedRidgePartner_deletion_eq {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (i : Fin n) :
    (representedRidgePartner P gap).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using
      P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using P.prefixChain_flipSignAt_last_succAbove i

theorem deletion_gap_eq_of_prefixChain_eq {d : ℕ} (hd : 0 < d)
    {P Q : SignedPermutation (d + 1)} {gap eta : Fin (d + 1)}
    (hdel :
      ∀ a : Fin d,
        Q.prefixChain (eta.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    eta = gap := by
  apply Fin.succAbove_left_injective
  funext a
  apply Fin.ext
  have hcard :=
    congrArg (fun X : NonzeroSignedSubset (d + 1) => X.1.card) (hdel a)
  have hcard' :
      (eta.succAbove a).val + 1 = (gap.succAbove a).val + 1 := by
    simpa [SignedPermutation.prefixChain_card] using hcard
  omega

theorem eq_or_flipSignAt_last_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain ((Fin.last n).succAbove a) =
          P.prefixChain ((Fin.last n).succAbove a)) :
    Q = P ∨ Q = P.flipSignAt (Fin.last n) := by
  have hprefix_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hatom_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hi
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_last i hi
    · intro j hj
      apply hprefix_ne_last
      intro hjlast
      have hivallast : i.val = n + 1 := by
        rw [← hj, hjlast]
        simp [Fin.last]
      exact Nat.ne_of_lt i.isLt hivallast
  have horder_last : Q.order (Fin.last n) = P.order (Fin.last n) := by
    let k : Fin (n + 1) := P.order.symm (Q.order (Fin.last n))
    by_cases hk : k = Fin.last n
    · change Q.order (Fin.last n) = P.order (Fin.last n)
      calc
        Q.order (Fin.last n) = P.order k := by
          dsimp [k]
          simp
        _ = P.order (Fin.last n) := congrArg P.order hk
    · have hkorder : Q.order k = P.order k := (hatom_ne_last k hk).1
      have hPk : P.order k = Q.order (Fin.last n) := by
        dsimp [k]
        simp
      have hQeq : Q.order k = Q.order (Fin.last n) := hkorder.trans hPk
      exact False.elim (hk (Q.order.injective hQeq))
  by_cases hlastSign : Q.positive (Fin.last n) = P.positive (Fin.last n)
  · left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        exact hlastSign
      · exact (hatom_ne_last i hi).2
  · right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        cases hq : Q.positive (Fin.last n) <;>
          cases hp : P.positive (Fin.last n) <;>
            simp [flipSignAt, hq, hp] at hlastSign ⊢
      · simp [flipSignAt, hi, (hatom_ne_last i hi).2]

theorem eq_or_reindex_swap_of_internal_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨
      Q = P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hnext_val : next.val = gap.val + 1 := rfl
  have hnext_ne_gap : next ≠ gap := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [next, SignedPermutation.gapNext] at hval
    omega
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hprefix_ne_gap :
      ∀ i : Fin (n + 1), i ≠ gap → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hprefix_next : Q.prefixChain next = P.prefixChain next :=
    hprefix_ne_gap next hnext_ne_gap
  have hatom_fixed :
      ∀ i : Fin (n + 1), i ≠ gap → i ≠ next →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hig hinext
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_gap i hig
    · intro j hj
      apply hprefix_ne_gap
      intro hjgap
      apply hinext
      apply Fin.ext
      rw [← hj, hjgap]
      dsimp [next, SignedPermutation.gapNext]
  let xgap : Fin (n + 1) := Q.order gap
  have hxQnext : xgap ∈ (Q.prefixSignedSubset next).support := by
    exact (prefix_support_mem_order_iff Q xgap next).mpr (by
      change Q.order.symm (Q.order gap) ≤ next
      simpa [xgap] using hgap_le_next)
  have hsupport_next :
      (Q.prefixSignedSubset next).support = (P.prefixSignedSubset next).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support) hprefix_next
  have hxPnext : xgap ∈ (P.prefixSignedSubset next).support := by
    simpa [hsupport_next] using hxQnext
  have hPgap_le_next : P.order.symm xgap ≤ next :=
    (prefix_support_mem_order_iff P xgap next).mp hxPnext
  have hnot_lt_gap : ¬ P.order.symm xgap < gap := by
    intro hlt
    let j : Fin (n + 1) := P.order.symm xgap
    have hjne : j ≠ gap := by
      intro hj
      exact (ne_of_lt hlt) hj
    have hxPj : xgap ∈ (P.prefixSignedSubset j).support := by
      exact (prefix_support_mem_order_iff P xgap j).mpr (by simp [j])
    have hsupport_j :
        (Q.prefixSignedSubset j).support = (P.prefixSignedSubset j).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support)
          (hprefix_ne_gap j hjne)
    have hxQj : xgap ∈ (Q.prefixSignedSubset j).support := by
      simpa [hsupport_j] using hxPj
    have hqle : gap ≤ j := by
      simpa [xgap, j] using (prefix_support_mem_order_iff Q xgap j).mp hxQj
    exact not_lt_of_ge hqle hlt
  have hgap_le_Pgap : gap ≤ P.order.symm xgap := le_of_not_gt hnot_lt_gap
  have hPgap_cases :
      P.order.symm xgap = gap ∨ P.order.symm xgap = next := by
    have hge := Fin.le_iff_val_le_val.mp hgap_le_Pgap
    have hle := Fin.le_iff_val_le_val.mp hPgap_le_next
    have hnextv : next.val = gap.val + 1 := by
      dsimp [next, SignedPermutation.gapNext]
    by_cases hv : (P.order.symm xgap).val = gap.val
    · left
      exact Fin.ext hv
    · right
      apply Fin.ext
      omega
  have horder_gap_cases : Q.order gap = P.order gap ∨ Q.order gap = P.order next := by
    rcases hPgap_cases with hsymm | hsymm
    · left
      change xgap = P.order gap
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order gap := congrArg P.order hsymm
    · right
      change xgap = P.order next
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order next := congrArg P.order hsymm
  rcases horder_gap_cases with hgapOrder | hgapOrder
  · have hnextOrder : Q.order next = P.order next := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hknext : k = next
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order next := congrArg P.order hknext
      · by_cases hkgap : k = gap
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order gap := hgapOrder
              _ = P.order k := by rw [hkgap]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap.symm (Q.order.injective hQeq))
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next hgap_le_next
        hprefix_next
    have hnextSign : Q.positive next = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl le_rfl hprefix_next
    left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        exact hgapOrder
      · by_cases hin : i = next
        · subst i
          exact hnextOrder
        · exact (hatom_fixed i hig hin).1
    · funext i
      by_cases hig : i = gap
      · subst i
        exact hgapSign
      · by_cases hin : i = next
        · subst i
          exact hnextSign
        · exact (hatom_fixed i hig hin).2
  · have hnextOrder : Q.order next = P.order gap := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hkgap : k = gap
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order gap := congrArg P.order hkgap
      · by_cases hknext : k = next
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order next := hgapOrder
              _ = P.order k := by rw [hknext]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap (Q.order.injective hQeq).symm)
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next le_rfl
        hprefix_next
    have hnextSign : Q.positive next = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl hgap_le_next
        hprefix_next
    right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapOrder, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextOrder, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).1]
          change P.order i = P.order ((Equiv.swap gap next) i)
          rw [hswap]
    · funext i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapSign, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextSign, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).2]
          change P.positive i = P.positive ((Equiv.swap gap next) i)
          rw [hswap]

theorem eq_or_representedRidgePartner_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨ Q = representedRidgePartner P gap := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · rcases eq_or_reindex_swap_of_internal_deletion_eq P Q gap hgap hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    rcases eq_or_flipSignAt_last_of_deletion_eq P Q hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)

theorem reindex_swap_gap_prefix_le_next {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    SignedSubset.Le
      ((P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain gap).1
      (P.prefixChain (SignedPermutation.gapNext gap hgap)).1 := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hswap_le :
      ∀ k : Fin (n + 1), (Equiv.swap gap next) k ≤ gap → k ≤ next := by
    intro k hk
    by_cases hkg : k = gap
    · subst k
      exact hgap_le_next
    · by_cases hkn : k = next
      · subst k
        exact le_rfl
      · have hswap : (Equiv.swap gap next) k = k := by
          simp [Equiv.swap_apply_def, hkg, hkn]
        exact le_trans (by simpa [hswap] using hk) hgap_le_next
  constructor
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixNeg, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩

theorem flipSignAt_last_upperPrefixChain_of_not_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hnot : ¬ RepresentedUpperRidgeBoundary P (Fin.last n)) :
    UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hcoord : P.order.symm (Fin.last n) ≠ Fin.last n := by
    intro hcoord
    exact hnot ⟨rfl, hcoord⟩
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    intro hneg
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
        SignedPermutation.flipSignAt, hcoord] using hneg)
  · have hlt : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have heq :
        (P.flipSignAt (Fin.last n)).prefixChain i = P.prefixChain i :=
      P.prefixChain_flipSignAt_of_lt (j := Fin.last n) hlt
    simpa [heq] using hP i

theorem flipSignAt_last_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hcoord : P.order.symm (Fin.last n) = Fin.last n) :
    ¬ UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hposLast : P.positive (Fin.last n) := by
    by_contra hpos
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg, hcoord] using hpos)
  intro hflip
  exact hflip (Fin.last n) (by
    simp [UpperHemisphere, SignedPermutation.prefixChain,
      SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
      SignedPermutation.flipSignAt, hcoord, hposLast])

theorem representedRidgePartner_upperPrefixChain {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hnot : ¬ RepresentedUpperRidgeBoundary P gap) :
    UpperPrefixChain (representedRidgePartner P gap) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · intro i
    by_cases hi : i = gap
    · subst i
      simpa [hgap] using
        upperHemisphere_of_le (reindex_swap_gap_prefix_le_next P gap hgap)
          (hP (SignedPermutation.gapNext gap hgap))
    · have heq :
          (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain i =
            P.prefixChain i := by
        apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
        · exact SignedPermutation.gapNext_val gap hgap
        · exact hi
      simpa [hgap, heq] using hP i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using flipSignAt_last_upperPrefixChain_of_not_boundary P hP hnot

theorem representedRidgePartner_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hb : RepresentedUpperRidgeBoundary P gap) :
    ¬ UpperPrefixChain (representedRidgePartner P gap) := by
  rcases hb with ⟨hgapEq, hcoord⟩
  subst gap
  unfold representedRidgePartner
  have hgapLast : ¬ (Fin.last n).val < n := by
    simp [Fin.last]
  simpa [hgapLast] using flipSignAt_last_not_upperPrefixChain_of_boundary P hP hcoord

theorem last_mem_prefixPos_of_upper_of_order_le {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin (n + 1))
    (hupper : UpperHemisphere (P.prefixChain i))
    (hle : P.order.symm (Fin.last n) ≤ i) :
    Fin.last n ∈ (P.prefixChain i).1.pos := by
  by_cases hpos : P.positive (P.order.symm (Fin.last n))
  · simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, hle, hpos]
  · have hneg : Fin.last n ∈ (P.prefixChain i).1.neg := by
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hle, hpos]
    exact False.elim (hupper hneg)

/-- The local upper cofaces of a represented rho.  Boundary ridges retain only
the upper coface; interior ridges retain both local cofaces. -/
noncomputable def representedUpperRidgeLocalCofaces {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Finset (SignedPermutation (n + 1)) :=
  by
    classical
    exact
      if RepresentedUpperRidgeBoundary P gap then
        {P}
      else
        {P, representedRidgePartner P gap}

theorem representedUpperRidgeLocalCofaces_card {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (representedUpperRidgeLocalCofaces P gap).card =
      if RepresentedUpperRidgeBoundary P gap then 1 else 2 := by
  classical
  by_cases hb : RepresentedUpperRidgeBoundary P gap
  · rw [representedUpperRidgeLocalCofaces, if_pos hb, if_pos hb]
    simp
  · rw [representedUpperRidgeLocalCofaces, if_neg hb, if_neg hb]
    exact Finset.card_pair (representedRidgePartner_ne_self P gap).symm



/-! ## Actual upper-hemisphere label-set-`A` graph -/

noncomputable instance signedSubset_fintype (n : ℕ) : Fintype (SignedSubset n) := by
  classical
  refine Fintype.ofInjective (fun X : SignedSubset n => (X.pos, X.neg)) ?_
  intro X Y h
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance nonzeroSignedSubset_fintype (n : ℕ) :
    Fintype (NonzeroSignedSubset n) := by
  classical
  refine Fintype.ofInjective
    (fun X : NonzeroSignedSubset n => (X.1.pos, X.1.neg)) ?_
  intro X Y h
  apply Subtype.ext
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A concrete ordered codimension-one ridge in the upper hemisphere whose
retained labels are exactly `A`.  The ridge is an actual ordered chain of
vertices; the existential signed-permutation/gap field only certifies that it
is a genuine punctured maximal chain. -/
def ActualHemisphereARidge {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset (d + 1) //
    (∀ a : Fin d, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (d + 1), ∀ a : Fin d,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance actualHemisphereARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereARidge label) := by
  classical
  dsimp [ActualHemisphereARidge]
  infer_instance

/-- Upper-hemisphere maximal chains which contain at least one label-set-`A`
ridge. -/
def ActualHemisphereAChain {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {P : SignedPermutation (d + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (d + 1), ∀ a : Fin d,
        ∃ t : Fin d, label (P.prefixChain (gap.succAbove t)) = alternatingLabel a}

noncomputable instance actualHemisphereAChain_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereAChain label) := by
  classical
  dsimp [ActualHemisphereAChain]
  infer_instance

/-- Incidence between an actual ridge and an upper maximal chain: deleting one
rank of the chain gives exactly the ordered ridge. -/
def actualHemisphereAEdge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) (sigma : ActualHemisphereAChain label) : Prop :=
  ∃ gap : Fin (d + 1), ∀ a : Fin d,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAEdge_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidableRel (actualHemisphereAEdge (label := label)) := by
  classical
  exact inferInstance

/-- Boundary ridges are exactly those whose retained vertices all lie in the
equator. -/
def actualHemisphereABoundary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) : Prop :=
  ∀ a : Fin d, Equator (rho.1 a)

noncomputable instance actualHemisphereABoundary_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereABoundary (label := label)) := by
  classical
  exact inferInstance

/-- Unordered maximal label-set-`A` objects on the equator, expressed in the
same data language as `ActualHemisphereARidge`: the vertices are transported
through `equatorEquiv`, and the maximal-equator witness is a boundary punctured
flag in the upper hemisphere. -/
def EquatorActualARidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset d //
    (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last d) ∧
        ∀ a : Fin d,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last d).succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance equatorActualARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype (EquatorActualARidge label) := by
  classical
  dsimp [EquatorActualARidge]
  infer_instance

theorem actualHemisphereABoundary_iff_represented {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereABoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last d := by
      by_contra hne
      have hlast_ne_gap : Fin.last d ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last d ∈ (P.prefixChain (Fin.last d)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last d) (hP (Fin.last d))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last d) = Fin.last d := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last d ∈ (P.prefixChain (P.order.symm (Fin.last d))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last d))
          (hP (P.order.symm (Fin.last d))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

noncomputable def equatorBoundaryARidgeEquiv {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    {rho : ActualHemisphereARidge label // actualHemisphereABoundary rho} ≃
      EquatorActualARidge (equatorRestrictedLabel label) where
  toFun rho := by
    classical
    let dropped : Fin d → NonzeroSignedSubset d :=
      fun a => (equatorEquiv d).symm ⟨rho.1.1 a, rho.2 a⟩
    have hrepr :
        ∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
          RepresentedUpperRidgeBoundary P (Fin.last d) ∧
            ∀ a : Fin d,
              equatorEmbed (dropped a) =
                P.prefixChain ((Fin.last d).succAbove a) := by
      rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
      have hb := (actualHemisphereABoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
      rcases hb with ⟨hgap, hcoord⟩
      subst gap
      refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
      intro a
      calc
        equatorEmbed (dropped a) = rho.1.1 a := by
          dsimp [dropped, equatorEquiv]
          exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
        _ = P.prefixChain ((Fin.last d).succAbove a) := hrho a
    refine ⟨dropped, hrepr, ?_⟩
    intro a
    rcases rho.1.2.2.2 a with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    dsimp [dropped, equatorRestrictedLabel, equatorEquiv]
    simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht
  invFun rho := by
    classical
    let lifted : Fin d → NonzeroSignedSubset (d + 1) := fun a => equatorEmbed (rho.1 a)
    have hupper : ∀ a : Fin d, UpperHemisphere (lifted a) := by
      intro a
      exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
    let hactual : ActualHemisphereARidge label :=
      ⟨lifted, by
        refine ⟨hupper, ?_, ?_⟩
        · rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
          exact ⟨P, hP, ⟨Fin.last d, hrepr⟩⟩
        · intro a
          rcases rho.2.2 a with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          dsimp [lifted, equatorRestrictedLabel, equatorEquiv] at ht ⊢
          simpa using ht⟩
    refine ⟨hactual, ?_⟩
    intro a
    change Equator (equatorEmbed (rho.1 a))
    exact equatorEmbed_mem_equator (rho.1 a)
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp
    exact equatorDrop_equatorEmbed (rho.1 a)

def KyFanUnorderedParityStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset d → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card (EquatorActualARidge label))



/-- A top chain is one-door when deleting exactly one of its vertices leaves
the alternating label set `A`. -/
def actualHemisphereAOneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) : Prop :=
  (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereAOneDoor_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereAOneDoor (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereAIncidentRepresentedCofaceEquiv {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereAChain label // actualHemisphereAEdge rho sigma} ≃
      {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (d + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin d, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hd (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin d,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2.1))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin d, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    let sigma : ActualHemisphereAChain label :=
      ⟨Q.1, hQupper, ⟨gap, fun a => by
        rcases rho.2.2.2 a with ⟨t, ht⟩
        exact ⟨t, by simpa [hQdel t] using ht⟩⟩⟩
    exact ⟨sigma, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereA_rho_degree_card {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) :
    Fintype.card
        {sigma : ActualHemisphereAChain label //
          actualHemisphereAEdge rho sigma} =
      if actualHemisphereABoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereAIncidentRepresentedCofaceEquiv hd rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereABoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereABoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualRidgeOfChainGap {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    ActualHemisphereARidge label :=
  ⟨fun a : Fin d => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2.1 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2.1, ⟨gap.1, fun a => rfl⟩⟩,
      fun a => by
        rcases gap.2 a with ⟨t, htne, htlabel⟩
        rcases Fin.exists_succAbove_eq htne with ⟨b, hb⟩
        exact ⟨b, by simpa [← hb] using htlabel⟩⟩⟩

theorem actualRidgeOfChainGap_edge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    actualHemisphereAEdge (actualRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereAEdge_gives_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {rho : ActualHemisphereARidge label} {sigma : ActualHemisphereAChain label}
    (hedge : actualHemisphereAEdge rho sigma) :
    ∃ gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j},
      rho = actualRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdoor : SigmaDeletionHasAlternatingLabelSet
      (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases rho.2.2.2 a with ⟨b, hb⟩
    exact ⟨gap.succAbove b, Fin.succAbove_ne gap b, by
      simpa [← hgap b] using hb⟩
  refine ⟨⟨gap, hdoor⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualRidgeOfChainGap_injective {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Function.Injective (actualRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereAIncidentDoorEquiv {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} ≃
      {j : Fin (d + 1) //
        SigmaDeletionHasAlternatingLabelSet
          (fun i => label (sigma.1.prefixChain i)) j} where
  toFun rho :=
    Classical.choose (actualHemisphereAEdge_gives_door rho.2)
  invFun gap :=
    ⟨actualRidgeOfChainGap sigma gap, actualRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereAEdge_gives_door rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereAEdge_gives_door (actualRidgeOfChainGap_edge sigma gap))
    apply actualRidgeOfChainGap_injective sigma
    exact hspec.symm









noncomputable def actualHemisphereRhoDegreeDataOfDegreeCard {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label))
    (hdegree :
      ∀ rho : ActualHemisphereARidge label,
        Fintype.card
            {sigma : ActualHemisphereAChain label //
              actualHemisphereAEdge rho sigma} =
          if actualHemisphereABoundary rho then 1 else 2) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) where
  edge := actualHemisphereAEdge
  edge_decidable := actualHemisphereAEdge_decidable
  boundary := actualHemisphereABoundary
  boundary_decidable := actualHemisphereABoundary_decidable
  nonempty_R := hR
  degree_card := hdegree

noncomputable def actualHemisphereRhoDegreeData {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label)) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
  actualHemisphereRhoDegreeDataOfDegreeCard hR
    (actualHemisphereA_rho_degree_card hd)

/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/

def ActualHemisphereIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxRidge idx label) := by
  classical
  dsimp [ActualHemisphereIdxRidge]
  infer_instance

def ActualHemisphereIdxChain {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (r + 1), ∀ a : Fin r,
        ∃ t : Fin r,
          label (P.prefixChain (gap.succAbove t)) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxChain_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxChain idx label) := by
  classical
  dsimp [ActualHemisphereIdxChain]
  infer_instance

def actualHemisphereIdxEdge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereIdxEdge_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereIdxEdge (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereIdxBoundary {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereIdxBoundary_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxBoundary (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def EquatorActualIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance equatorActualIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualIdxRidge idx label) := by
  classical
  dsimp [EquatorActualIdxRidge]
  infer_instance





















def actualHemisphereIdxOneDoor {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereIdxOneDoor_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxOneDoor (idx := idx) (label := label)) := by
  classical
  exact inferInstance

























/-! ## Actual upper-hemisphere graph with self-contained alternating labels -/

def ActualHemisphereAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance actualHemisphereAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltRidge label) := by
  classical
  dsimp [ActualHemisphereAltRidge]
  infer_instance

def ActualHemisphereAltChain {r m : ℕ}
    (_label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) // UpperPrefixChain P}

noncomputable instance actualHemisphereAltChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltChain label) := by
  classical
  dsimp [ActualHemisphereAltChain]
  infer_instance

def actualHemisphereAltEdge {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (sigma : ActualHemisphereAltChain label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAltEdge_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereAltEdge (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereAltBoundary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereAltBoundary_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltBoundary (label := label)) := by
  classical
  exact inferInstance

theorem actualHemisphereAltBoundary_iff_represented {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereAltBoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last r := by
      by_contra hne
      have hlast_ne_gap : Fin.last r ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last r ∈ (P.prefixChain (Fin.last r)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last r) (hP (Fin.last r))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last r) = Fin.last r := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last r ∈ (P.prefixChain (P.order.symm (Fin.last r))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last r))
          (hP (P.order.symm (Fin.last r))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

def actualHemisphereAltTop {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) : Prop :=
  IsAltPos label (fun i : Fin (r + 1) => sigma.1.prefixChain i) ∨
    IsAltNeg label (fun i : Fin (r + 1) => sigma.1.prefixChain i)

noncomputable instance actualHemisphereAltTop_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltTop (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereAltIncidentRepresentedCofaceEquiv {r m : ℕ}
    (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltEdge rho sigma} ≃
      {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (r + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin r, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hr (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin r,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin r, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    exact ⟨⟨Q.1, hQupper⟩, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereAlt_rho_degree_card {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label) :
    Fintype.card
        {sigma : ActualHemisphereAltChain label //
          actualHemisphereAltEdge rho sigma} =
      if actualHemisphereAltBoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereAltIncidentRepresentedCofaceEquiv hr rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereAltBoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereAltBoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualAltRidgeOfChainGap {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label)
    (gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))}) :
    ActualHemisphereAltRidge label :=
  ⟨fun a : Fin r => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2, ⟨gap.1, fun a => rfl⟩⟩,
      gap.2⟩⟩

theorem actualAltRidgeOfChainGap_edge {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label)
    (gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))}) :
    actualHemisphereAltEdge (actualAltRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereAltEdge_gives_gap {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    {rho : ActualHemisphereAltRidge label}
    {sigma : ActualHemisphereAltChain label}
    (hedge : actualHemisphereAltEdge rho sigma) :
    ∃ gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))},
      rho = actualAltRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdel : IsAltPos label (fun a : Fin r => sigma.1.prefixChain (gap.succAbove a)) := by
    have hfun :
        (fun a : Fin r => sigma.1.prefixChain (gap.succAbove a)) = rho.1 := by
      funext a
      exact (hgap a).symm
    rw [hfun]
    exact rho.2.2.2
  refine ⟨⟨gap, hdel⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualAltRidgeOfChainGap_injective {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    Function.Injective (actualAltRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereAltIncidentDeletionEquiv {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltEdge rho sigma} ≃
      {j : Fin (r + 1) //
        IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))} where
  toFun rho :=
    Classical.choose (actualHemisphereAltEdge_gives_gap rho.2)
  invFun gap :=
    ⟨actualAltRidgeOfChainGap sigma gap, actualAltRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereAltEdge_gives_gap rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereAltEdge_gives_gap (actualAltRidgeOfChainGap_edge sigma gap))
    apply actualAltRidgeOfChainGap_injective sigma
    exact hspec.symm









noncomputable def actualHemisphereAltRhoDegreeData {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereAltRidge label)) :
    RhoDegreeManifoldData
      (ActualHemisphereAltRidge label) (ActualHemisphereAltChain label) where
  edge := actualHemisphereAltEdge
  edge_decidable := actualHemisphereAltEdge_decidable
  boundary := actualHemisphereAltBoundary
  boundary_decidable := actualHemisphereAltBoundary_decidable
  nonempty_R := hR
  degree_card := actualHemisphereAlt_rho_degree_card hr



def EquatorActualAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance equatorActualAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAltRidge label) := by
  classical
  dsimp [EquatorActualAltRidge]
  infer_instance

noncomputable def equatorBoundaryAltRidgeToEquator {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : {rho : ActualHemisphereAltRidge label //
      actualHemisphereAltBoundary rho}) :
    EquatorActualAltRidge (equatorRestrictedLabelOf label) := by
  classical
  let dropped : Fin r → NonzeroSignedSubset r :=
    fun a => (equatorEquiv r).symm ⟨rho.1.1 a, rho.2 a⟩
  have hrepr :
      ∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        RepresentedUpperRidgeBoundary P (Fin.last r) ∧
          ∀ a : Fin r,
            equatorEmbed (dropped a) =
              P.prefixChain ((Fin.last r).succAbove a) := by
    rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
    have hb := (actualHemisphereAltBoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
    rcases hb with ⟨hgap, hcoord⟩
    subst gap
    refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
    intro a
    calc
      equatorEmbed (dropped a) = rho.1.1 a := by
        dsimp [dropped, equatorEquiv]
        exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
      _ = P.prefixChain ((Fin.last r).succAbove a) := hrho a
  have halt : IsAltPos (equatorRestrictedLabelOf label) dropped := by
    rcases rho.1.2.2.2 with ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hx' : label (rho.1.1 a) ∈ simplexLabelSet label rho.1.1 := by
        simp [simplexLabelSet]
      rw [hset] at hx'
      convert hx' using 1
      dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv] at ha ⊢
      simpa [equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)] using ha.symm
    · intro hx
      have hx' : x ∈ simplexLabelSet label rho.1.1 := by
        rw [hset]
        exact hx
      rcases Finset.mem_image.mp hx' with ⟨t, _ht, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv]
      simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht
  exact ⟨dropped, hrepr, halt⟩

noncomputable def equatorBoundaryAltRidgeFromEquator {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : EquatorActualAltRidge (equatorRestrictedLabelOf label)) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltBoundary rho} := by
  classical
  let lifted : Fin r → NonzeroSignedSubset (r + 1) := fun a => equatorEmbed (rho.1 a)
  have hupper : ∀ a : Fin r, UpperHemisphere (lifted a) := by
    intro a
    exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
  have halt : IsAltPos label lifted := by
    rcases rho.2.2 with ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hx' :
          equatorRestrictedLabelOf label (rho.1 a) ∈
            simplexLabelSet (equatorRestrictedLabelOf label) rho.1 := by
        simp [simplexLabelSet]
      rw [hset] at hx'
      convert hx' using 1
      dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv] at ha ⊢
      simpa using ha.symm
    · intro hx
      have hx' :
          x ∈
            simplexLabelSet (equatorRestrictedLabelOf label) rho.1 := by
        rw [hset]
        exact hx
      rcases Finset.mem_image.mp hx' with ⟨t, _ht, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv]
      simpa using ht
  let hactual : ActualHemisphereAltRidge label :=
    ⟨lifted, by
      refine ⟨hupper, ?_, halt⟩
      rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
      exact ⟨P, hP, ⟨Fin.last r, hrepr⟩⟩⟩
  refine ⟨hactual, ?_⟩
  intro a
  change Equator (equatorEmbed (rho.1 a))
  exact equatorEmbed_mem_equator (rho.1 a)

noncomputable def equatorBoundaryAltRidgeEquiv {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltBoundary rho} ≃
      EquatorActualAltRidge (equatorRestrictedLabelOf label) where
  toFun := equatorBoundaryAltRidgeToEquator
  invFun := equatorBoundaryAltRidgeFromEquator
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryAltRidgeToEquator, equatorBoundaryAltRidgeFromEquator]
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryAltRidgeToEquator, equatorBoundaryAltRidgeFromEquator]
    exact equatorDrop_equatorEmbed (rho.1 a)



/-! ## Antipodal and hemisphere bridges for self-contained alternating chains -/

theorem labelSeqSet_alternatingLabelOf {k m : ℕ} (idx : Fin k → Fin m) :
    labelSeqSet (fun a : Fin k => alternatingLabelOf idx a) = alternatingLabelSetOf idx := by
  simp [labelSeqSet, alternatingLabelSetOf]

theorem IsAltPosLabelSeq.not_isAltNeg {k m : ℕ} (hk : 0 < k)
    {L : Fin k → SignedLabel m} :
    IsAltPosLabelSeq L → IsAltNegLabelSeq L → False := by
  classical
  rintro ⟨idx, hidx, hsetPos⟩ hneg
  let Lpos : Fin k → SignedLabel m := fun a => alternatingLabelOf idx a
  have hLposSet : labelSeqSet Lpos = labelSeqSet L := by
    rw [hsetPos]
    exact labelSeqSet_alternatingLabelOf idx
  have hnegPos : IsAltNegLabelSeq Lpos := by
    rcases hneg with ⟨eta, heta, hsetNeg⟩
    exact ⟨eta, heta, hLposSet.trans hsetNeg⟩
  let sgn : Fin k → Bool := fun a => decide (Even a.val)
  have hLpos :
      ∀ a : Fin k, Lpos a = { positive := sgn a, index := idx a } := by
    intro a
    rfl
  have hsgnNeg : signSeqAltNeg sgn :=
    (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hLpos).mp hnegPos
  let i : Fin k := ⟨0, hk⟩
  have hi := hsgnNeg i
  simp [signSeqAltNeg, sgn, i] at hi

theorem IsAltPos.not_isAltNeg {k m n : ℕ} (hk : 0 < k)
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltPos label sigma → IsAltNeg label sigma → False :=
  IsAltPosLabelSeq.not_isAltNeg hk

theorem IsAltPosLabelSeq_neg_iff_isAltNeg {k m : ℕ} {L : Fin k → SignedLabel m} :
    IsAltPosLabelSeq (fun a => (L a).neg) ↔ IsAltNegLabelSeq L := by
  classical
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      have hxneg : x.neg ∈ labelSeqSet (fun a : Fin k => (L a).neg) := by
        rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
        refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
        rw [← ha]
      rw [hset] at hxneg
      rcases (by simpa [alternatingLabelSetOf] using hxneg) with ⟨a, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
      rw [ha]
      simp [SignedLabel.neg]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxpos : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
        simp [alternatingLabelSetOf]
      rw [← hset] at hxpos
      rcases Finset.mem_image.mp hxpos with ⟨b, _hb, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha]
      have hb' := congrArg SignedLabel.neg hb
      apply SignedLabel.ext
      · simpa [SignedLabel.neg] using congrArg SignedLabel.positive hb'
      · simpa [SignedLabel.neg] using congrArg SignedLabel.index hb'
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxneg : L a ∈ alternatingNegLabelSetOf idx := by
        rw [← hset]
        simp [labelSeqSet]
      rcases (by simpa [alternatingNegLabelSetOf] using hxneg) with ⟨b, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha, ← hb]
      simp [SignedLabel.neg, alternatingLabelOf]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxorig : (alternatingLabelOf idx a).neg ∈ labelSeqSet L := by
        rw [hset]
        simp [alternatingNegLabelSetOf]
      rcases Finset.mem_image.mp hxorig with ⟨b, _hb, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha, hb]
      simp [SignedLabel.neg, alternatingLabelOf]

theorem IsAltNegLabelSeq_neg_iff_isAltPos {k m : ℕ} {L : Fin k → SignedLabel m} :
    IsAltNegLabelSeq (fun a => (L a).neg) ↔ IsAltPosLabelSeq L := by
  constructor
  · intro h
    have h' :=
      (IsAltPosLabelSeq_neg_iff_isAltNeg
        (L := fun a : Fin k => (L a).neg)).mpr h
    simpa [SignedLabel.neg] using h'
  · intro h
    apply (IsAltPosLabelSeq_neg_iff_isAltNeg
      (L := fun a : Fin k => (L a).neg)).mp
    simpa [SignedLabel.neg] using h

theorem IsAltPos_antipode_iff_isAltNeg {m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    IsAltPos label (fun i : Fin n => P.antipode.prefixChain i) ↔
      IsAltNeg label (fun i : Fin n => P.prefixChain i) := by
  have hfun :
      (fun i : Fin n => label (P.antipode.prefixChain i)) =
        fun i : Fin n => (label (P.prefixChain i)).neg := by
    funext i
    rw [SignedPermutation.prefixChain_antipode]
    exact hantipodal (P.prefixChain i)
  change
    IsAltPosLabelSeq (fun i : Fin n => label (P.antipode.prefixChain i)) ↔
      IsAltNegLabelSeq (fun i : Fin n => label (P.prefixChain i))
  rw [hfun]
  exact IsAltPosLabelSeq_neg_iff_isAltNeg

theorem IsAltNeg_antipode_iff_isAltPos {m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    IsAltNeg label (fun i : Fin n => P.antipode.prefixChain i) ↔
      IsAltPos label (fun i : Fin n => P.prefixChain i) := by
  have hfun :
      (fun i : Fin n => label (P.antipode.prefixChain i)) =
        fun i : Fin n => (label (P.prefixChain i)).neg := by
    funext i
    rw [SignedPermutation.prefixChain_antipode]
    exact hantipodal (P.prefixChain i)
  change
    IsAltNegLabelSeq (fun i : Fin n => label (P.antipode.prefixChain i)) ↔
      IsAltPosLabelSeq (fun i : Fin n => label (P.prefixChain i))
  rw [hfun]
  exact IsAltNegLabelSeq_neg_iff_isAltPos

theorem upperPrefixChain_iff_last_positive {n : ℕ} (P : SignedPermutation (n + 1)) :
    UpperPrefixChain P ↔ P.positive (P.order.symm (Fin.last n)) := by
  constructor
  · intro hupper
    by_contra hpos
    exact hupper (P.order.symm (Fin.last n)) (by
      simp [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg, hpos])
  · intro hpos i hneg
    have hmem : Fin.last n ∈ (P.prefixChain i).1.neg := hneg
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixNeg, hpos] at hmem

theorem upperPrefixChain_antipode_iff_not {n : ℕ} (P : SignedPermutation (n + 1)) :
    UpperPrefixChain P.antipode ↔ ¬ UpperPrefixChain P := by
  rw [upperPrefixChain_iff_last_positive P.antipode,
    upperPrefixChain_iff_last_positive P]
  simp [SignedPermutation.antipode]

@[simp]
theorem finPredOfNotLast_castSucc {r : ℕ} (i : Fin r)
    (h : Fin.castSucc i ≠ Fin.last r) :
    finPredOfNotLast (Fin.castSucc i) h = i := by
  apply Fin.ext
  rfl

noncomputable def equatorExtendOrder {r : ℕ} (e : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r + 1)) where
  toFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e (finPredOfNotLast i hi))
  invFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e.symm (finPredOfNotLast i hi))
  left_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]
  right_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e.symm (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]



@[simp]
theorem equatorExtendOrder_symm_apply_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    (equatorExtendOrder e).symm (Fin.last r) = Fin.last r := by
  simp [equatorExtendOrder]



@[simp]
theorem equatorExtendOrder_symm_apply_castSucc {r : ℕ} (e : Equiv.Perm (Fin r))
    (i : Fin r) :
    (equatorExtendOrder e).symm (Fin.castSucc i) = Fin.castSucc (e.symm i) := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [equatorExtendOrder, h]

noncomputable def signedPermutationEquatorExtend {r : ℕ}
    (P : SignedPermutation r) : SignedPermutation (r + 1) where
  order := equatorExtendOrder P.order
  positive := fun i =>
    if hi : i = Fin.last r then true
    else P.positive (finPredOfNotLast i hi)





theorem signedPermutationEquatorExtend_upperPrefixChain {r : ℕ}
    (P : SignedPermutation r) :
    UpperPrefixChain (signedPermutationEquatorExtend P) := by
  rw [upperPrefixChain_iff_last_positive]
  simp [signedPermutationEquatorExtend]

theorem signedPermutationEquatorExtend_boundary {r : ℕ}
    (P : SignedPermutation r) :
    RepresentedUpperRidgeBoundary (signedPermutationEquatorExtend P) (Fin.last r) := by
  exact ⟨rfl, by simp [signedPermutationEquatorExtend]⟩

theorem signedPermutationEquatorExtend_prefixChain_castSucc {r : ℕ}
    (P : SignedPermutation r) (i : Fin r) :
    (signedPermutationEquatorExtend P).prefixChain (Fin.castSucc i) =
      equatorEmbed (P.prefixChain i) := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend, Fin.castSucc_le_castSucc_iff]
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend, Fin.castSucc_le_castSucc_iff]

theorem equatorEmbed_injective {r : ℕ} :
    Function.Injective (@equatorEmbed r) := by
  intro X Y h
  exact (equatorEquiv r).injective (Subtype.ext h)

theorem signedPermutation_eq_of_prefixChain_eq {n : ℕ}
    (P Q : SignedPermutation n)
    (hprefix : ∀ i : Fin n, Q.prefixChain i = P.prefixChain i) :
    Q = P := by
  apply SignedPermutation.ext_order_positive
  · apply Equiv.ext
    intro i
    exact (order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
      (hprefix i) (fun j _hj => hprefix j)).1
  · funext i
    exact (order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
      (hprefix i) (fun j _hj => hprefix j)).2

theorem perm_apply_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    e (Fin.last r) = Fin.last r := by
  calc
    e (Fin.last r) = e (e.symm (Fin.last r)) := by rw [hcoord]
    _ = Fin.last r := by simp

theorem perm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e.symm hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

theorem perm_symm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e.symm (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [perm_apply_last_of_symm_last e hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

noncomputable def equatorDropOrder {r : ℕ} (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    Equiv.Perm (Fin r) where
  toFun i :=
    finPredOfNotLast (e (Fin.castSucc i))
      (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  invFun i :=
    finPredOfNotLast (e.symm (Fin.castSucc i))
      (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  left_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e.symm
              (Fin.castSucc
                (finPredOfNotLast (e (Fin.castSucc i))
                  (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e (Fin.castSucc i))
                (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e.symm
          (Fin.castSucc
            (finPredOfNotLast (e (Fin.castSucc i))
              (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e.symm (e (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp
  right_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e
              (Fin.castSucc
                (finPredOfNotLast (e.symm (Fin.castSucc i))
                  (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e.symm (Fin.castSucc i))
                (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e
          (Fin.castSucc
            (finPredOfNotLast (e.symm (Fin.castSucc i))
              (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e (e.symm (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp



@[simp]
theorem equatorDropOrder_symm_apply_castSucc {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    Fin.castSucc ((equatorDropOrder e hcoord).symm i) =
      e.symm (Fin.castSucc i) := by
  dsimp [equatorDropOrder]
  rw [castSucc_finPredOfNotLast]

noncomputable def signedPermutationEquatorDrop {r : ℕ}
    (P : SignedPermutation (r + 1))
    (hcoord : P.order.symm (Fin.last r) = Fin.last r) :
    SignedPermutation r where
  order := equatorDropOrder P.order hcoord
  positive := fun i => P.positive (Fin.castSucc i)

theorem signedPermutationEquatorDrop_prefixChain_castSucc {r : ℕ}
    (P : SignedPermutation (r + 1))
    (hcoord : P.order.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    equatorEmbed ((signedPermutationEquatorDrop P hcoord).prefixChain i) =
      P.prefixChain (Fin.castSucc i) := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hcoord]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      have hleiff :
          ((equatorDropOrder P.order hcoord).symm y ≤ i) ↔
            P.order.symm (Fin.castSucc y) ≤ Fin.castSucc i := by
        constructor
        · intro hle
          rw [← equatorDropOrder_symm_apply_castSucc P.order hcoord y]
          exact Fin.castSucc_le_castSucc_iff.mpr hle
        · intro hle
          apply Fin.castSucc_le_castSucc_iff.mp
          rwa [equatorDropOrder_symm_apply_castSucc P.order hcoord y]
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hleiff]
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hcoord]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      have hleiff :
          ((equatorDropOrder P.order hcoord).symm y ≤ i) ↔
            P.order.symm (Fin.castSucc y) ≤ Fin.castSucc i := by
        constructor
        · intro hle
          rw [← equatorDropOrder_symm_apply_castSucc P.order hcoord y]
          exact Fin.castSucc_le_castSucc_iff.mpr hle
        · intro hle
          apply Fin.castSucc_le_castSucc_iff.mp
          rwa [equatorDropOrder_symm_apply_castSucc P.order hcoord y]
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hleiff]

def FullAltPosChain {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {P : SignedPermutation r // IsAltPos label (fun i : Fin r => P.prefixChain i)}

noncomputable instance fullAltPosChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (FullAltPosChain label) := by
  classical
  dsimp [FullAltPosChain]
  infer_instance

noncomputable def fullAltPosToEquatorActualAltRidge {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (P : FullAltPosChain label) :
    EquatorActualAltRidge label := by
  classical
  refine ⟨fun i : Fin r => P.1.prefixChain i, ?_, P.2⟩
  refine ⟨signedPermutationEquatorExtend P.1,
    signedPermutationEquatorExtend_upperPrefixChain P.1,
    signedPermutationEquatorExtend_boundary P.1, ?_⟩
  intro a
  simpa [Fin.succAbove_last] using
    (signedPermutationEquatorExtend_prefixChain_castSucc P.1 a).symm

noncomputable def equatorActualAltRidgeToFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (rho : EquatorActualAltRidge label) :
    FullAltPosChain label := by
  classical
  let P : SignedPermutation (r + 1) := Classical.choose rho.2.1
  have hspec :
      UpperPrefixChain P ∧ RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho.1 a) = P.prefixChain ((Fin.last r).succAbove a) :=
    Classical.choose_spec rho.2.1
  let Q : SignedPermutation r := signedPermutationEquatorDrop P hspec.2.1.2
  have hprefix : ∀ a : Fin r, Q.prefixChain a = rho.1 a := by
    intro a
    apply equatorEmbed_injective
    calc
      equatorEmbed (Q.prefixChain a) = P.prefixChain (Fin.castSucc a) := by
        exact signedPermutationEquatorDrop_prefixChain_castSucc P hspec.2.1.2 a
      _ = P.prefixChain ((Fin.last r).succAbove a) := by
        simp [Fin.succAbove_last]
      _ = equatorEmbed (rho.1 a) := (hspec.2.2 a).symm
  refine ⟨Q, ?_⟩
  have hfun : (fun i : Fin r => Q.prefixChain i) = rho.1 := by
    funext i
    exact hprefix i
  simpa [hfun] using rho.2.2

theorem equatorActualAltRidgeToFullAltPos_prefixChain {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (rho : EquatorActualAltRidge label) (i : Fin r) :
    (equatorActualAltRidgeToFullAltPos rho).1.prefixChain i = rho.1 i := by
  classical
  unfold equatorActualAltRidgeToFullAltPos
  dsimp
  let P : SignedPermutation (r + 1) := Classical.choose rho.2.1
  have hspec :
      UpperPrefixChain P ∧ RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho.1 a) = P.prefixChain ((Fin.last r).succAbove a) :=
    Classical.choose_spec rho.2.1
  apply equatorEmbed_injective
  calc
    equatorEmbed ((signedPermutationEquatorDrop P hspec.2.1.2).prefixChain i) =
        P.prefixChain (Fin.castSucc i) := by
      exact signedPermutationEquatorDrop_prefixChain_castSucc P hspec.2.1.2 i
    _ = P.prefixChain ((Fin.last r).succAbove i) := by
      simp [Fin.succAbove_last]
    _ = equatorEmbed (rho.1 i) := (hspec.2.2 i).symm

noncomputable def equatorActualAltRidgeEquivFullAltPos {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    EquatorActualAltRidge label ≃ FullAltPosChain label where
  toFun := equatorActualAltRidgeToFullAltPos
  invFun := fullAltPosToEquatorActualAltRidge
  left_inv := by
    intro rho
    apply Subtype.ext
    funext i
    exact equatorActualAltRidgeToFullAltPos_prefixChain rho i
  right_inv := by
    intro P
    apply Subtype.ext
    apply signedPermutation_eq_of_prefixChain_eq P.1
    intro i
    simpa [fullAltPosToEquatorActualAltRidge] using
      equatorActualAltRidgeToFullAltPos_prefixChain
        (fullAltPosToEquatorActualAltRidge P) i



noncomputable def upperTopToFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (sigma : {sigma : ActualHemisphereAltChain label //
      actualHemisphereAltTop sigma}) :
    FullAltPosChain label := by
  classical
  let P : SignedPermutation (r + 1) := sigma.1.1
  by_cases hpos : IsAltPos label (fun i : Fin (r + 1) => P.prefixChain i)
  · exact ⟨P, hpos⟩
  · have hneg : IsAltNeg label (fun i : Fin (r + 1) => P.prefixChain i) := by
      rcases sigma.2 with h | h
      · exact False.elim (hpos h)
      · exact h
    exact ⟨P.antipode, (IsAltPos_antipode_iff_isAltNeg hantipodal P).mpr hneg⟩

noncomputable def fullAltPosToUpperTop {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : FullAltPosChain label) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} := by
  classical
  by_cases hupper : UpperPrefixChain P.1
  · exact ⟨⟨P.1, hupper⟩, Or.inl P.2⟩
  · have hupperAnti : UpperPrefixChain P.1.antipode :=
      (upperPrefixChain_antipode_iff_not P.1).mpr hupper
    have hnegAnti :
        IsAltNeg label (fun i : Fin (r + 1) => P.1.antipode.prefixChain i) :=
      (IsAltNeg_antipode_iff_isAltPos hantipodal P.1).mpr P.2
    exact ⟨⟨P.1.antipode, hupperAnti⟩, Or.inr hnegAnti⟩

noncomputable def upperTopEquivFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} ≃
      FullAltPosChain label where
  toFun := upperTopToFullAltPos hantipodal
  invFun := fullAltPosToUpperTop hantipodal
  left_inv := by
    intro sigma
    classical
    dsimp [upperTopToFullAltPos, fullAltPosToUpperTop]
    let P : SignedPermutation (r + 1) := sigma.1.1
    have hupper : UpperPrefixChain P := sigma.1.2
    by_cases hpos : IsAltPos label (fun i : Fin (r + 1) => P.prefixChain i)
    · simp [P, hpos, hupper]
    · have hnotUpperAnti : ¬ UpperPrefixChain P.antipode := by
        intro h
        exact (upperPrefixChain_antipode_iff_not P).mp h hupper
      simp [P, hpos, hnotUpperAnti]
      apply Subtype.ext
      apply Subtype.ext
      exact SignedPermutation.antipode_involutive P
  right_inv := by
    intro P
    classical
    dsimp [upperTopToFullAltPos, fullAltPosToUpperTop]
    by_cases hupper : UpperPrefixChain P.1
    · have hposP : IsAltPos label (fun i : Fin (r + 1) => P.1.prefixChain i) := P.2
      simp [hupper, hposP]
    · have hupperAnti : UpperPrefixChain P.1.antipode :=
        (upperPrefixChain_antipode_iff_not P.1).mpr hupper
      have hnotPosAnti :
          ¬ IsAltPos label (fun i : Fin (r + 1) => P.1.antipode.prefixChain i) := by
        intro hposAnti
        have hnegP :
            IsAltNeg label (fun i : Fin (r + 1) => P.1.prefixChain i) :=
          (IsAltPos_antipode_iff_isAltNeg hantipodal P.1).mp hposAnti
        exact IsAltPos.not_isAltNeg (Nat.succ_pos r) P.2 hnegP
      simp [hupper, hupperAnti, hnotPosAnti]
      apply Subtype.ext
      exact SignedPermutation.antipode_involutive P.1



theorem IsAltPos_one_iff_positiveAlternatingPrefixLabels {m : ℕ}
    (label : NonzeroSignedSubset 1 → SignedLabel m)
    (P : SignedPermutation 1) :
    IsAltPos label (fun i : Fin 1 => P.prefixChain i) ↔
      PositiveAlternatingPrefixLabels label P := by
  classical
  constructor
  · rintro ⟨idx, _hidx, hset⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a
      fin_cases b
      omega
    · intro i
      fin_cases i
      have hmem :
          label (P.prefixChain 0) ∈
            alternatingLabelSetOf idx := by
        have hmemSimplex :
            label (P.prefixChain 0) ∈
              simplexLabelSet label (fun i : Fin 1 => P.prefixChain i) := by
          simp [simplexLabelSet]
        simpa [hset] using hmemSimplex
      have hlabel :
          label (P.prefixChain 0) = alternatingLabelOf idx 0 := by
        simpa [alternatingLabelSetOf] using hmem
      simpa [alternatingLabelOf] using
        congrArg SignedLabel.positive hlabel
  · rintro ⟨hstrict, hsign⟩
    refine ⟨fun i : Fin 1 => (label (P.prefixChain i)).index, hstrict, ?_⟩
    have hlabel :
        label (P.prefixChain 0) =
          alternatingLabelOf
            (fun i : Fin 1 => (label (P.prefixChain i)).index) 0 := by
      apply SignedLabel.ext
      · simpa [alternatingLabelOf] using hsign 0
      · rfl
    ext x
    constructor
    · intro hx
      have hx0 : x = label (P.prefixChain 0) := by
        simpa [simplexLabelSet] using hx
      rw [hx0]
      simp [alternatingLabelSetOf, hlabel]
    · intro hx
      have hx0 :
          x =
            alternatingLabelOf
              (fun i : Fin 1 => (label (P.prefixChain i)).index) 0 := by
        simpa [alternatingLabelSetOf] using hx
      rw [hx0]
      simp [simplexLabelSet, hlabel]

noncomputable def fullAltPosChainEquivPositiveAlternatingPrefixLabelChains_one
    {m : ℕ} (label : NonzeroSignedSubset 1 → SignedLabel m) :
    FullAltPosChain label ≃
      {P : SignedPermutation 1 // P ∈ positiveAlternatingPrefixLabelChains label} where
  toFun P :=
    ⟨P.1, by
      classical
      have hpos :
          PositiveAlternatingPrefixLabels label P.1 :=
        (IsAltPos_one_iff_positiveAlternatingPrefixLabels label P.1).mp P.2
      simpa [positiveAlternatingPrefixLabelChains, hpos]⟩
  invFun P :=
    ⟨P.1, by
      classical
      apply (IsAltPos_one_iff_positiveAlternatingPrefixLabels label P.1).mpr
      have hmem := P.2
      change P.1 ∈
        (Finset.univ.filter fun P : SignedPermutation 1 =>
          PositiveAlternatingPrefixLabels label P) at hmem
      exact (Finset.mem_filter.mp hmem).2⟩
  left_inv := by
    intro P
    rfl
  right_inv := by
    intro P
    rfl







theorem strictMono_fin_self_eq_id {d : ℕ} {idx : Fin d → Fin d}
    (hidx : StrictMono idx) :
    idx = fun i => i := by
  funext i
  exact le_antisymm (StrictMono.le_id hidx i) (StrictMono.id_le hidx i)

theorem IsAltPos_iff_label_set_A {d : ℕ}
    {label : NonzeroSignedSubset d → SignedLabel d}
    {rho : Fin d → NonzeroSignedSubset d} :
    IsAltPos label rho ↔
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a := by
  classical
  constructor
  · rintro ⟨idx, hidx, hset⟩ a
    have hidxId : idx = fun i : Fin d => i :=
      strictMono_fin_self_eq_id hidx
    subst idx
    have hmemAlt :
        alternatingLabel a ∈
          alternatingLabelSetOf (fun i : Fin d => i) := by
      simp [alternatingLabelSetOf, alternatingLabelOf, alternatingLabel]
    have hmemSimplex :
        alternatingLabel a ∈ simplexLabelSet label rho := by
      simpa [hset] using hmemAlt
    rcases (by simpa [simplexLabelSet] using hmemSimplex) with ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro hA
    refine ⟨fun i : Fin d => i, (fun _ _ h => h), ?_⟩
    have hsubset :
        alternatingLabelSetOf (fun i : Fin d => i) ⊆
          simplexLabelSet label rho := by
      intro x hx
      rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
      rcases hA a with ⟨t, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      rw [← ha]
      simpa [alternatingLabelOf, alternatingLabel] using ht
    have hsimplexCard :
        (simplexLabelSet label rho).card ≤ d := by
      dsimp [simplexLabelSet]
      calc
        (Finset.univ.image fun a : Fin d => label (rho a)).card ≤
            (Finset.univ : Finset (Fin d)).card :=
          Finset.card_image_le
        _ = d := by simp
    have hAltCard :
        (alternatingLabelSetOf (fun i : Fin d => i)).card = d :=
      alternatingLabelSetOf_card (Function.injective_id)
    have hcard :
        (simplexLabelSet label rho).card ≤
          (alternatingLabelSetOf (fun i : Fin d => i)).card := by
      simpa [hAltCard] using hsimplexCard
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

noncomputable def equatorActualARidgeEquivEquatorActualAltRidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    EquatorActualARidge label ≃ EquatorActualAltRidge label where
  toFun rho :=
    ⟨rho.1, rho.2.1, (IsAltPos_iff_label_set_A).mpr rho.2.2⟩
  invFun rho :=
    ⟨rho.1, rho.2.1, (IsAltPos_iff_label_set_A).mp rho.2.2⟩
  left_inv := by
    intro rho
    rfl
  right_inv := by
    intro rho
    rfl



/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/







def ActualHemisphereBoundaryOddStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card
          {rho : ActualHemisphereARidge label //
            actualHemisphereABoundary rho})

def EquatorBoundaryCardBridgeStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Fintype.card
            {rho : ActualHemisphereARidge label //
              actualHemisphereABoundary rho} =
          Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))





















end ProofsInTheBook.Chapter39

end


