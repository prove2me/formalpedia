-- Prove2me | Definitions.Def_Bridges_PrimeClosureLocale
-- name    : Bridges_PrimeClosureLocale
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:10.355476+00:00
-- url     : https://prove2.me/theorems/2d8e75a4-310d-4728-a7ba-a57e6916a895
-- title:
--   Aether Catalog definitions — Bridges_PrimeClosureLocale
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PrimeClosureLocale`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PrimeClosureLocale.lean by skeleton subtraction
import Mathlib
/-
# Prime Closure Locales and Computable Sheaf Semantics — Part I

This file establishes the **finite prime-closure locale** infrastructure: a computable
surrogate for spectral spaces that serves as the semantic phase space for proof-semiring
spectra, certified ML semantics, and post-quantum cryptographic consistency.

## Cross-domain bridges

* **Algebraic geometry ↔ Locale theory**: Compact opens form a meet-semilattice; presheaves
  restrict along inclusions, mimicking structure sheaves on affine schemes.
* **Proof semantics ↔ EML**: Local realizers are proof witnesses; global sections encode
  derivability; obstruction classes encode semantic inconsistency.
* **Cryptographic semantics**: Čech discrepancy measures semantic collision potential;
  vanishing obstruction certifies post-quantum gluing security.
* **Certified ML**: Local-to-global consistency of realizers yields Lipschitz-certified
  robustness of semantic predictions under cover perturbation.

## Main definitions

* `PrimeClosureLocale` — finite closure space with idempotent closure operator
* `CompactOpen` — finitely supported closed patches (computable semantic windows)
* `CompactOpen.inf` — meet of compact opens via intersection
* `LocalRealizerPresheaf` — restriction-compatible local realizer assignment
* `ConstantPresheaf` — constant presheaf model (anchor for provability)

## References

The closure-operator axiomatics follow the standard Kuratowski closure axioms specialized to
the finite setting. The presheaf structure is a direct categorical formulation of a
contravariant functor on the poset of compact opens.
-/


set_option maxHeartbeats 400000

universe u v w

/-! ## Section 1: Prime Closure Locale -/

/-- A finite closure-locale used as a computable semantic phase space for
proof-semiring spectra.

Bridge: algebraic geometry ↔ certified ML ↔ post-quantum cryptography.

The closure operator axiomatizes the semantic saturation of proof obligations:
`closure S` is the smallest semantically complete extension of a set of local
realizers `S`. The idempotency axiom (`closure_idem`) ensures that semantic
saturation stabilizes in finite time—a key computability guarantee. -/
structure PrimeClosureLocale (α : Type u) where
  /-- The finite carrier set representing the prime spectrum. -/
  carrier : Finset α
  /-- Predicate for closed sets in the closure topology. -/
  isClosed : Set α → Prop
  /-- The full space is closed. -/
  univ_closed : isClosed Set.univ
  /-- Closed sets are closed under binary intersection. -/
  inter_closed : ∀ s t, isClosed s → isClosed t → isClosed (s ∩ t)
  /-- Closure operator on subsets. -/
  closure : Set α → Set α
  /-- Every set is contained in its closure. -/
  subset_closure : ∀ s, s ⊆ closure s
  /-- The closure of any set is closed. -/
  closure_closed : ∀ s, isClosed (closure s)
  /-- Closure is the smallest closed superset. -/
  closure_min : ∀ s t, s ⊆ t → isClosed t → closure s ⊆ t
  /-- Closure is idempotent—semantic saturation stabilizes. -/
  closure_idem : ∀ s, closure (closure s) = closure s

namespace PrimeClosureLocale

variable {α : Type u} (L : PrimeClosureLocale α)






end PrimeClosureLocale

/-! ## Section 2: Compact Opens -/

/-- Compact opens are represented by finitely-supported closed patches.
In the finite setting, these are computable semantic windows—observable
fragments of the proof-semiring spectrum.

Bridge: compact opens in algebraic geometry correspond to decidable
semantic predicates in ML certification and finitely testable security
properties in post-quantum cryptography. -/
structure CompactOpen (α : Type u) [DecidableEq α] (L : PrimeClosureLocale α) where
  /-- The finite support of this compact open. -/
  support : Finset α
  /-- The support, viewed as a set, is closed. -/
  is_compact_open : L.isClosed (↑support : Set α)

namespace CompactOpen

variable {α : Type u} [DecidableEq α] {L : PrimeClosureLocale α}

/-- The ordering on compact opens: inclusion of supports.
Bridge: refinement ordering on semantic observation windows. -/
instance instLE : LE (CompactOpen α L) where
  le U V := (↑U.support : Set α) ⊆ (↑V.support : Set α)



/-- Meet (intersection) of two compact opens.
Bridge: joint observation window / conjunction of security predicates. -/
def inf (U V : CompactOpen α L) : CompactOpen α L where
  support := U.support ∩ V.support
  is_compact_open := by
    have h : (↑(U.support ∩ V.support) : Set α) = (↑U.support : Set α) ∩ (↑V.support : Set α) := by
      ext x; simp [Finset.mem_coe, Finset.mem_inter]
    rw [h]
    exact L.inter_closed _ _ U.is_compact_open V.is_compact_open







end CompactOpen

/-! ## Section 3: Local Realizer Presheaf -/


namespace LocalRealizerPresheaf

variable {α : Type u} [DecidableEq α] {β : Type v} {L : PrimeClosureLocale α}


end LocalRealizerPresheaf

/-! ## Section 4: Constant Presheaf -/


/-! ## Section 5: Compatibility and Čech Data -/








/-! ## Section 6: Quantitative Bounds -/





/-  The lines below are corrupted leftovers of a text edit: each is the tail of a
    statement whose head was lost.  They are kept, commented out, for the record;
    without the comment the file does not parse.

    end AgreementOnInter F (s V hV) (s W hW)
-/


