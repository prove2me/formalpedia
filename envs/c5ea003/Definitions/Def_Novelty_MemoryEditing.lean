-- Prove2me | Definitions.Def_Novelty_MemoryEditing
-- name    : Novelty_MemoryEditing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:51.104492+00:00
-- url     : https://prove2.me/theorems/30d5d986-b7ae-4f4e-93a8-ac72d44b8320
-- title:
--   Aether Catalog definitions — Novelty_MemoryEditing
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MemoryEditing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MemoryEditing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_LeftDivisibility
/-
# Memory Editing: When Forgetting Is a Mathematical Operation

We model a **memory** as a structure-preserving map from *experience streams* to
*compressed representations*.  Experience streams accumulate by concatenation, so
the natural home for a stream is a monoid; a compressed representation is another
monoid `N`, and a memory is a monoid homomorphism `f : M →* N`.  The empty stream
maps to the neutral representation, and remembering two experiences one after the
other agrees with remembering their concatenation: `f (s * t) = f s * f t`.

The **finite-memory bound** is the hypothesis that the space of representations is
finite (`Finite N`): a real agent stores memories in bounded space.  Against an
unbounded stream space (`Infinite M`, e.g. arbitrarily long streams over a
nonempty alphabet) this forces *forgetting*.

This file establishes four structural facts.

* **Forced loss (`finite_memory_forces_loss`).**  Any memory obeying a
  finite-memory bound over an unbounded stream space is *lossy*: distinct streams
  are inevitably confused.  This is a hard limit, independent of how the memory is
  engineered.

* **Loss is algebraic (`confusion`, `finite_memory_confusion_nontrivial`).**  The
  set of *confusable pairs* `{(s,t) | f s = f t}` is a **submonoid** of `M × M`:
  confusion is closed under concatenation and contains the empty pair.  Forgetting
  is not a random glitch — it has algebraic structure.  Under a finite-memory
  bound this submonoid strictly contains the diagonal, so genuine (off-diagonal)
  loss occurs.

* **Targeted forgetting is a quotient (`forgetting_is_quotient`,
  `compressedEquivQuotient`, `kerLift_lossless`).**  A *forgetting policy* is a
  congruence `c` on the stream monoid; the canonical projection `M →* c.Quotient`
  is a surjective memory whose confusion is exactly `c`.  Conversely every memory
  `f` factors through the quotient by its confusion congruence, and the induced map
  out of the quotient is **injective**: all information loss happens at the
  quotient step, after which the representation is faithful.  The compressed image
  is isomorphic to that quotient.

* **Compression respects temporal order (`memory_preserves_leftDvd`,
  `memory_preserves_prefix`).**  Building on the left-divisibility order of
  `Catalog.Novelty.LeftDivisibility`, a memory is monotone for the "is an initial
  segment of" order: if stream `a` is a prefix of stream `b`, then the compressed
  `f a` still divides `f b`.  Forgetting may merge experiences, but it never
  reverses their temporal precedence.

-- !-- Lab Notes -- !--

HYPOTHESIS (Hypothesizer).
  H1 (bold). A finite-memory monoid homomorphism from an unbounded stream monoid
     *must* be lossy — a pigeonhole limit with no engineering escape.
  H2 (surprising, structural). The set of confused stream pairs is not merely a
     set but a *submonoid* of `M × M`: information loss composes.
  H3 (grand challenge). "Targeted forgetting" is not an ad-hoc deletion but is
     *exactly* the quotient construction: forgetting policies = congruences =
     quotient monoids, with the first-isomorphism factorisation showing the
     quotient is the unique faithful compression.
  H4 (cross-domain: algebra × order). Compression is monotone for the temporal
     (prefix / left-divisibility) order on streams.

EXPERIMENT (Experimenter).
  - Loss via `Finite.exists_ne_map_eq_of_infinite`.
  - `confusion` assembled as a `Submonoid (M × M)` using `map_mul`.
  - Congruence machinery: `Con.ker`, `Con.mk'`, `Con.quotientKerEquivRange`,
    `Con.kerLift`/`Con.kerLift_injective` for the factorisation.
  - Order bridge reuses `UphoMultiplicability.LeftDvd` and
    `freeMonoid_leftDvd_iff_isPrefix` from the catalog.

ANALYSIS (Analyst).
  Everything survived. The decisive structural insight: the *same* congruence
  `Con.ker f` plays three roles — it is the confusion relation, it is the
  forgetting policy, and it is the kernel of the quotient projection. Loss,
  policy, and quotient coincide. Groups would collapse the order bridge (their
  divisibility order is indiscrete, cf. the catalog), so the stream monoid must be
  a genuinely non-group monoid (free monoids being the prototype).

CRITIQUE (Critic).
  - `finite_memory_forces_loss` is non-vacuous: `FreeMonoid α` over nonempty `α`
    is genuinely infinite, so the corollary `stream_memory_lossy` bites.
  - `confusion` is not the trivial diagonal: `finite_memory_confusion_nontrivial`
    exhibits an off-diagonal member.
  - `kerLift_lossless` guards against the misreading that quotients still lose
    information: they do not; loss is entirely localised to the projection.
  - No theorem is `True`/`rfl`-only; each uses pigeonhole, congruence, or the
    submonoid closure law.

SYNTHESIS (PI).
  Memory = monoid hom; forgetting = confusion congruence = quotient. The finite
  bound forces the confusion congruence to be nontrivial, and the quotient by it
  is the canonical faithful compression. See `FUTURE_DIRECTIONS.md`.
-/

namespace MemoryEditing

open Function UphoMultiplicability

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

/-! ## Information loss as a submonoid -/

/-- The **confusion submonoid** of a memory `f : M →* N`: the pairs of experience
streams that `f` renders indistinguishable.  It is closed under concatenation
(`(a,b),(c,d) ↦ (a*c, b*d)`) and contains the empty pair, hence is a genuine
submonoid of `M × M` — information loss has algebraic structure. -/
def confusion (f : M →* N) : Submonoid (M × M) where
  carrier := {p | f p.1 = f p.2}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]



/-! ## Finite memory forces forgetting -/

/-- A memory is **lossy** when it fails to be injective: some two distinct streams
collapse to the same representation. -/
def Lossy (f : M →* N) : Prop := ¬ Function.Injective f





/-! ## Targeted forgetting is a quotient -/







/-! ## Compression respects temporal order (algebra × order bridge) -/



end MemoryEditing


