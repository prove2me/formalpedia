-- Prove2me | Definitions.Def_Bridges_BerggrenTransferDuality
-- name    : Bridges_BerggrenTransferDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:49.825325+00:00
-- url     : https://prove2.me/theorems/bcce1829-95d8-422f-89ca-aa0ee4e57d19
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTransferDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTransferDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTransferDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Berggren Transfer Duality via Triple-Tree Scattering Semimodules

This file establishes a formal bridge between **Berggren arithmetic dynamics** of primitive
Pythagorean triples, **weighted automata / Hankel realization theory**, and
**idempotent transfer physics**.

## Main Results

The core insight is that a finite arithmetic tree (Berggren subtree) is recoverable from
transfer observables exactly as a finite scattering object is recoverable from its
response data.

### Key Theorems

1. `prefixClosed_nil_mem` — Every nonempty prefix-closed set contains the root word.
2. `prefixClosed_prefix_mem` — Prefix-closed sets are closed under taking prefixes.
3. `boundaryWords_finite` — The boundary of a finite set is finite.
4. `futureEquiv_equivalence` — Future-equivalence is an equivalence relation.
5. `finiteRankHankel_of_finite_prefix_closed_support` — Finite support implies finite
   Hankel rank (the core Hankel finiteness theorem).
6. `finiteRankHankel_iff_finiteResonanceType` — Finite Hankel rank is equivalent to finite
   resonance type for prefix-closed languages.
7. `berggren_transfer_duality` — Existence of transfer duality for finite Berggren subtrees.
8. `certified_reconstruction_from_observables` — Certified reconstruction of the minimal
   resonance automaton from observable data.
9. `spectral_shell_decomposition` — Depth-shell decomposition of finite Berggren subtrees.
10. `transfer_observables_determine_boundary_partition` — Transfer observables determine
    the boundary resonance partition.

## Mathematical Context

- **Arithmetic inverse scattering**: Finite Berggren subtrees behave like compact scatterers,
  with root-to-boundary paths as channels and transfer weights as propagation amplitudes.
- **Weighted automata**: Pythagorean triple generation is recast as a 3-letter deterministic
  production system with semiring-valued observables.
- **Tropical resonance**: In idempotent semirings, addition models competition of channels,
  multiplication models propagation, and finite decomposition corresponds to finitely many
  dominant resonant modes.

## References

- Berggren (1934): "Pytagoreiska trianglar"
- Fliess (1974): Hankel matrices and rational series
- Berstel–Reutenauer: Rational series and their languages

## Keywords

arithmetic inverse scattering, Berggren tree realization, weighted automata,
Hankel minimality, idempotent transfer semimodules, tropical resonance,
certified reconstruction, discrete scattering channels, Pythagorean spectral shells,
arithmetic interference invariants, formal inverse problems, semiring signal processing
-/

noncomputable section

open Set Finset List

/-! ## 1. Berggren Alphabet and Word Type -/

/-- The three Berggren generators, corresponding to the three standard matrices
    that generate all primitive Pythagorean triples from (3,4,5).
    - `A`: the matrix [[1,-2,2],[2,-1,2],[2,-2,3]]
    - `B`: the matrix [[1,2,2],[2,1,2],[2,2,3]]
    - `C`: the matrix [[-1,2,2],[-2,1,2],[-2,2,3]] -/
inductive BerggrenGen : Type
  | A : BerggrenGen
  | B : BerggrenGen
  | C : BerggrenGen
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- A Berggren word is a finite sequence of Berggren generators, encoding a path
    in the Berggren ternary tree from root to a descendant triple. -/
abbrev BerggrenWord := List BerggrenGen

instance : DecidableEq BerggrenWord := inferInstance

/-! ## 2. Prefix-Closure and Tree Structure -/

/-- A set of words is **prefix-closed** if every prefix of a member is also a member.
    This captures the tree structure: if a node is in the subtree, so is every ancestor. -/
def prefixClosed (B : Set BerggrenWord) : Prop :=
  ∀ ⦃u v⦄, u ++ v ∈ B → u ∈ B


/-- The **boundary** (leaf set) of a set of words: words in B none of whose
    one-step extensions is in B. These are the "scattering boundary states." -/
def boundaryWords (B : Set BerggrenWord) : Set BerggrenWord :=
  { w ∈ B | ∀ g : BerggrenGen, w ++ [g] ∉ B }

/-- The **interior** of a set of words: words in B having at least one child in B. -/
def interiorWords (B : Set BerggrenWord) : Set BerggrenWord :=
  { w ∈ B | ∃ g : BerggrenGen, w ++ [g] ∈ B }


/-! ## 3. Transfer Observables and Hankel Kernel -/

/-- The **transfer Hankel kernel** maps pairs of words to an observable value
    by concatenating and observing. This is the discrete scattering matrix. -/
def transferHankel {R : Type*} (Obs : BerggrenWord → R) (u v : BerggrenWord) : R :=
  Obs (u ++ v)

/-- Path weight in a semiring, computed as the product of generator weights along the path. -/
def pathWeight {R : Type*} [Monoid R] (wgt : BerggrenGen → R) : BerggrenWord → R
  | [] => 1
  | g :: t => wgt g * pathWeight wgt t

/-- The **future function** of a word w maps extensions v to Obs(w ++ v). -/
def futureFun {R : Type*} (Obs : BerggrenWord → R) (w : BerggrenWord) : BerggrenWord → R :=
  fun v => Obs (w ++ v)

/-! ## 4. Resonance Equivalence -/

/-- Two words are **future-equivalent** (resonance-equivalent) if they produce the same
    transfer response to all future extensions. This is the Myhill-Nerode relation
    for weighted automata / discrete scattering. -/
def FutureEquiv {R : Type*} (Obs : BerggrenWord → R) (u v : BerggrenWord) : Prop :=
  ∀ x : BerggrenWord, Obs (u ++ x) = Obs (v ++ x)

/-- **Finite Hankel rank**: the set of distinct future functions is finite.
    This is the weighted-automata analogue of having finitely many Nerode classes. -/
def FiniteRankHankel {R : Type*} (Obs : BerggrenWord → R) : Prop :=
  Set.Finite (Set.range (futureFun Obs))

/-- **Finite resonance type**: the image of B under the future-function map is finite.
    I.e., there are finitely many observationally distinct states in the subtree. -/
def FiniteResonanceType {R : Type*} (B : Set BerggrenWord) (Obs : BerggrenWord → R) : Prop :=
  Set.Finite (futureFun Obs '' B)



/-! ## 5. Minimal Transfer Presentation -/




/-! ## 6. Resonance Automaton -/





/-! ## 7. Shell Decomposition -/

/-- A **shell decomposition** partitions B by depth level. -/
def ShellDecomposition (B : Set BerggrenWord) (shells : ℕ → Set BerggrenWord) : Prop :=
  (∀ n, shells n ⊆ B) ∧
  (∀ w ∈ B, w ∈ shells w.length) ∧
  (∀ n m, n ≠ m → Disjoint (shells n) (shells m))


/-- Arithmetic factor sensitivity: an invariant that detects when words produce
    triples sharing arithmetic features. -/
def ArithmeticFactorSensitive (B : Set BerggrenWord)
    (I : BerggrenWord → BerggrenWord → Prop) : Prop :=
  (∀ w₁ w₂, I w₁ w₂ → w₁ ∈ B ∧ w₂ ∈ B) ∧
  (∀ w, w ∈ B → I w w) ∧
  (∀ w₁ w₂, I w₁ w₂ → I w₂ w₁) ∧
  (∀ w₁ w₂ w₃, I w₁ w₂ → I w₂ w₃ → I w₁ w₃)

/-- Transfer degeneracy detection: the interference invariant is detected by
    equality of transfer futures restricted to B. -/
def TransferDegeneracyDetectedBy (B : Set BerggrenWord) (Obs : BerggrenWord → ℕ∞)
    (I : BerggrenWord → BerggrenWord → Prop) : Prop :=
  ∀ w₁ ∈ B, ∀ w₂ ∈ B, FutureEquiv Obs w₁ w₂ → I w₁ w₂

/-! ## 8. Basic Structural Theorems -/








/-! ## 9. Future-Equivalence is an Equivalence Relation -/








/-! ## 10. Core Hankel Finiteness Theorems -/






/-! ## 11. Transfer Duality and Reconstruction Theorems -/



/-! ## 12. Spectral Shell Decomposition -/



/-! ## 13. Path Weight Lemmas -/




/-! ## 14. Certified Reconstruction -/


/-! ## 15. Hankel Kernel Properties -/






/-! ## 16. BerggrenGen Enumeration -/

/-- The list of all Berggren generators. -/
def BerggrenGen.all : List BerggrenGen := [.A, .B, .C]



/-! ## 17. Depth-Filtered Observables -/

/-- The depth filtration restricts an observable to words of bounded depth. -/
def depthFilteredObs {R : Type*} [Zero R] (Obs : BerggrenWord → R) (N : ℕ) :
    BerggrenWord → R :=
  fun w => if w.length ≤ N then Obs w else 0



/-! ## 18. Connection to Tropical Choquet Theory

The future function map provides a tropical capacity interpretation:
each word's future function is a "test observable" in the sense of
tropical Choquet decomposition theory.

This connects to `certified_finite_tropical_decomposition` from
`Bridges.AlgebraEML.TropicalChoquetClosureDuality`: the finite set of
future functions generated by a Berggren subtree plays the role of the
finite support in the tropical max functional, and the Hankel rank
corresponds to the cardinality of the irredundant tropical support.

The certified tropical decomposition guarantees:
1. The tropical functional (transfer kernel) is sup-preserving
2. The generating futures (weights) are uniquely determined
3. The decomposition is irredundant (all generators are essential)

This is precisely the formal content needed for certified inverse
reconstruction of Berggren subtrees from transfer data.
-/


/-! ## 19. Prefix-Closed Set Structural Lemmas -/




/-! ## 20. Future Function Right-Extension -/



end


