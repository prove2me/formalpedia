-- Prove2me | Definitions.Def_Novelty_HilbertClassFieldReciprocity
-- name    : Novelty_HilbertClassFieldReciprocity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:33.3902+00:00
-- url     : https://prove2.me/theorems/843804b4-0564-4ce9-aa28-7c3ced929acc
-- title:
--   Aether Catalog definitions — Novelty_HilbertClassFieldReciprocity
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HilbertClassFieldReciprocity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HilbertClassFieldReciprocity.lean by skeleton subtraction
import Mathlib
/-
# Hilbert class fields via the Artin reciprocity isomorphism

Hilbert's twelfth problem asks for an *explicit* generalization of Kronecker–Weber to arbitrary
number fields.  The first structural step beyond the cyclotomic (`GL(1)/ℚ`) case treated in
`Catalog.Novelty.CyclotomicGL1Langlands` is the **Hilbert class field** `H` of a number field
`K`: the maximal unramified abelian extension, characterized by the Artin reciprocity
isomorphism

  `Gal(H/K) ≃ Cl(𝒪_K)`

between its Galois group and the ideal class group of the ring of integers of `K`.

Because the full existence theory of the Hilbert class field (maximality, unramifiedness) is not
yet available in Mathlib, we formalize its *defining reciprocity property* as an explicit
hypothesis — a group isomorphism `e : Gal(H/K) ≃* ClassGroup 𝒪_K` — and derive the two invariants
that make the object useful:

* `HilbertClassFieldReciprocity.finrank_eq_classNumber` — **the degree equals the class number**:
  `[H : K] = h_K`.  This is the numerical heart of class field theory.
* `HilbertClassFieldReciprocity.finrank_one_of_classNumber_one` — **class number one forces
  triviality**: if `h_K = 1` then `[H : K] = 1`, i.e. a field of class number one is its own
  Hilbert class field.

To certify that these statements are *not vacuous*, `witnessRat` exhibits the reciprocity
isomorphism concretely for `K = H = ℚ` (both `Gal(ℚ/ℚ)` and `Cl(ℤ)` are trivial), and
`finrank_rat_eq_classNumber` instantiates the main theorem there.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The bold GL(1)→general step is `Gal(H/K) ≃ Cl(𝒪_K)`.  Even without a
Mathlib construction of `H`, the reciprocity isomorphism alone should *force* `[H:K] = h_K` and
collapse the extension when `h_K = 1`.  This is the natural Hilbert-12 analogue of the cyclotomic
degree computation `[ℚ(ζₙ):ℚ] = φ(n)` from the sibling file.

Experiment (Experimenter): Combined `IsGalois.card_aut_eq_finrank` (`#Gal = [H:K]`) with
`Nat.card_congr e.toEquiv` (`#Gal = #Cl`) and the definitional
`classNumber K = Fintype.card (ClassGroup 𝒪_K)`.  The chain closed with a single `rw`.  The
`h_K = 1 ⇒ [H:K] = 1` corollary is immediate.  Non-vacuousness (`witnessRat`) required a
`Subsingleton` instance on `Cl(ℤ)` obtained from `Rat.classNumber_eq` via
`Fintype.card_le_one_iff_subsingleton`.

Analysis (Analyst): "True conditionally on the reciprocity datum, and non-vacuous." The result
is genuine explicit class field theory: it turns the abstract isomorphism into the arithmetic
degree identity `[H:K] = h_K`.  The `ℚ` witness rules out the failure mode "the hypotheses can
never be met."  Distinguishing feature vs. Kronecker–Weber: here the reciprocity target is the
class group, a nonabelian-era invariant, whereas over `ℚ` it degenerates to `(ZMod n)ˣ`.

Critique (Critic): The reciprocity isomorphism `e` is a genuine, load-bearing hypothesis (drop
it and the degree identity is false in general), not a hidden `True`.  The proof uses real
structure (`card_aut_eq_finrank`, `card_congr`), not `decide`.  The witness prevents vacuity.

Synthesis (PI): This packages the "degree = class number" law as a reusable lemma keyed only on
the Artin reciprocity isomorphism — the exact interface a future Mathlib Hilbert-class-field
construction would plug into.
-- !-- Lab Notes -- !--
-/

open NumberField

namespace HilbertClassFieldReciprocity



/-- **Non-vacuity witness.**  For `K = H = ℚ`, the reciprocity isomorphism exists: both
`Gal(ℚ/ℚ)` and `Cl(ℤ)` are trivial groups, so there is a (unique) group isomorphism between
them.  This certifies that the hypotheses of `finrank_eq_classNumber` are satisfiable. -/
noncomputable def witnessRat : (ℚ ≃ₐ[ℚ] ℚ) ≃* ClassGroup (RingOfIntegers ℚ) := by
  haveI : Subsingleton (ClassGroup (RingOfIntegers ℚ)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)
  refine MulEquiv.mk ⟨fun _ => 1, fun _ => 1, ?_, ?_⟩ ?_
  · intro x; exact Subsingleton.elim _ _
  · intro x; exact Subsingleton.elim _ _
  · intro a b; exact (one_mul 1).symm


end HilbertClassFieldReciprocity


