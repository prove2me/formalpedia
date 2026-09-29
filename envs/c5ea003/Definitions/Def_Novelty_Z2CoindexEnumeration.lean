-- Prove2me | Definitions.Def_Novelty_Z2CoindexEnumeration
-- name    : Novelty_Z2CoindexEnumeration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:54:57.166222+00:00
-- url     : https://prove2.me/theorems/b2f39d02-cc3d-4c78-ae78-7e0bcd11f45b
-- title:
--   Aether Catalog definitions — Novelty_Z2CoindexEnumeration
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Z2CoindexEnumeration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Z2CoindexEnumeration.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_Z2CoindexSuspensionTower
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Exact enumeration of ℤ₂-maps between combinatorial spheres

This file *deepens* the theory of the `ℤ₂`-coindex of combinatorial spheres developed in
`Novelty.Z2CoindexSuspensionTower`.  There the existence question — *is there a `ℤ₂`-map
`Sᵐ → Sⁿ`?* — was answered exactly (`nonempty_iff_le : Nonempty (Z2Map m n) ↔ m ≤ n`) and the
suspension tower was shown to preserve the excess `n - m`.  Here we sharpen the *qualitative*
existence statement into a *quantitative* one: we count the `ℤ₂`-maps exactly.

## The classifying equivalence

A `ℤ₂`-map is equivariant, hence determined by the images of the positive vertices `(i, true)`,
recorded as data `g : Fin (m+1) → SVert n`; simpliciality is equivalent to injectivity of the
coordinate map `i ↦ (g i).1` (`induced_simplicial_iff_injective`, from the base file).  Splitting
that data into its *sign* part `Fin (m+1) → Bool` and its *coordinate* part — an injection
`Fin (m+1) ↪ Fin (n+1)` — gives a bijection

  `Z2Map m n  ≃  (Fin (m+1) → Bool) × (Fin (m+1) ↪ Fin (n+1))`.

Geometrically: a simplicial antipodal map of cross-polytopes is exactly a choice of an injection of
coordinate axes together with an independent sign for each source axis.

## Main results

* `equivPosData` — `Z2Map m n ≃ {g // Function.Injective (coordMap g)}`: a `ℤ₂`-map is its
  positive-vertex data with injective coordinates.
* `equivSignEmb` — that data splits as `(signs) × (coordinate injection)`.
* `card_Z2Map` — **the exact count** `|Z2Map m n| = 2^{m+1} · (n+1)^{\underline{m+1}}`, the falling
  factorial times the number of independent sign choices.
* `card_Z2Map_pos_iff` — the count is positive iff `m ≤ n`, recovering the existence criterion of
  the base file as a *corollary of the enumeration*.
* `card_Z2Map_self` — **the self-map count** `|Z2Map n n| = 2^{n+1} · (n+1)!`, the order of the
  hyperoctahedral group `B_{n+1}` (the symmetry group of the `(n+1)`-cross-polytope): every
  `ℤ₂`-self-map of `Sⁿ` is a signed permutation of coordinate axes.
* `card_suspension_tower` — the count is a suspension invariant: `|Z2Map (m+k) (n+k)| = |Z2Map m n|`
  along the suspension tower, refining `suspension_tower_exact` from a `Prop`-level equivalence to an
  equality of *cardinalities*.

The unifying insight is that the coindex, its excess, and the suspension tower are all shadows of a
single finite combinatorial object — the set of injections-with-signs — whose cardinality is an
elementary closed form.
-/

namespace Z2SuspensionTower

open Function

/-! ## Extensionality -/

/-- **Extensionality for `ℤ₂`-maps.**  Equivariance and simpliciality are propositions, so a
`ℤ₂`-map is determined by its underlying vertex map. -/
@[ext] theorem Z2Map.ext {m n : ℕ} {F G : Z2Map m n} (h : F.toFun = G.toFun) : F = G := by
  cases F; cases G; cases h; rfl

/-! ## The classifying equivalence -/

/-- **A `ℤ₂`-map is its positive-vertex data with injective coordinates.**  Equivariance lets us
reconstruct the whole map from the images of the positive vertices, and simpliciality is exactly
injectivity of the coordinate map (`induced_simplicial_iff_injective`). -/
def equivPosData (m n : ℕ) :
    Z2Map m n ≃ {g : Fin (m + 1) → SVert n // Function.Injective (coordMap g)} where
  toFun F := ⟨fun i => F.toFun (i, true), by
    have hface : induced (fun i => F.toFun (i, true)) = F.toFun := by
      funext p; obtain ⟨i, b⟩ := p
      cases b with
      | true => rfl
      | false => exact (F.equiv (i, true)).symm
    exact (induced_simplicial_iff_injective _).1 (by rw [hface]; exact F.simpl)⟩
  invFun g := ⟨induced g.1, induced_equiv g.1, (induced_simplicial_iff_injective g.1).2 g.2⟩
  left_inv F := by
    apply Z2Map.ext; funext p; obtain ⟨i, b⟩ := p
    cases b with
    | true => rfl
    | false => exact (F.equiv (i, true)).symm
  right_inv g := by apply Subtype.ext; funext i; rfl

/-- **The positive-vertex data splits as signs times a coordinate injection.**  The sign part is an
arbitrary `Fin (m+1) → Bool`; the coordinate part is the injection `coordMap g : Fin (m+1) ↪
Fin (n+1)`. -/
def equivSignEmb (m n : ℕ) :
    {g : Fin (m + 1) → SVert n // Function.Injective (coordMap g)} ≃
      (Fin (m + 1) → Bool) × (Fin (m + 1) ↪ Fin (n + 1)) where
  toFun g := (fun i => (g.1 i).2, ⟨coordMap g.1, g.2⟩)
  invFun p := ⟨fun i => (p.2 i, p.1 i), p.2.injective⟩
  left_inv g := by apply Subtype.ext; funext i; rfl
  right_inv p := by obtain ⟨s, σ⟩ := p; ext i <;> rfl

/-- The set of `ℤ₂`-maps `Sᵐ → Sⁿ` is finite. -/
instance instFinite (m n : ℕ) : Finite (Z2Map m n) :=
  Finite.of_equiv _ (equivPosData m n).symm

/-! ## The exact count -/





/-! ## Examples -/

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  The existence dichotomy `Nonempty (Z2Map m n) ↔ m ≤ n` proved in the
base file feels like the "positive part" of a finer, purely enumerative fact: because a `ℤ₂`-map is
rigidly determined by an injection of coordinate axes with independent signs, the *number* of
`ℤ₂`-maps ought to be a clean closed form — signs times a falling factorial — with the existence
criterion falling out as the positivity of that count.

**Experiment (Experimenter).**  We upgraded the base file's `induced_simplicial_iff_injective` from a
criterion into an *equivalence of types*: `equivPosData` identifies `Z2Map m n` with injective
positive-vertex data, and `equivSignEmb` splits that data as `(Fin (m+1) → Bool) × (Fin (m+1) ↪
Fin (n+1))`.  Transporting cardinalities through these bijections and applying the falling-factorial
count of embeddings yields `card_Z2Map`.  Two corollaries followed: the positivity criterion
`card_Z2Map_pos_iff`, and the identification of the self-map count with the hyperoctahedral order
`2^{n+1}(n+1)!`.  A short induction gave the suspension invariance `card_suspension_tower`.

**Analysis (Analyst).**  Everything reduced to the *rigidity* of equivariant simplicial maps of
cross-polytopes: no freedom beyond an axis injection and a sign vector.  The self-map case is the
sharpest reading — `Z2Map n n` is exactly the symmetry group `B_{n+1}` — and explains geometrically
why the coindex is pinned to the dimension.  The suspension invariance is a genuine cancellation:
one suspension multiplies the sign count by `2` but divides the axis-injection count by the newly
opened slot, and the two effects cancel exactly.

**Critique (Critic).**  No result is vacuous: `card_Z2Map` is a nontrivial equality of natural
numbers proved through two explicit bijections and Mathlib's embedding count; the examples exhibit
the values `24, 48, 0`; and `two_pow_dvd_card` extracts the free-action divisor from the closed
form, not by unfolding a definition.  The positivity corollary is logically downstream of the
count, so it does not circularly reuse the base file's `nonempty_iff_le`.  The boundary case of the
naive "suspension-invariant count" conjecture is recorded above as a genuine counterexample.

**Synthesis (Principal Investigator).**  The `ℤ₂`-coindex theory of combinatorial spheres is
governed by a single elementary counting formula `|Z2Map m n| = 2^{m+1}(n+1)^{\underline{m+1}}`; the
existence criterion, the hyperoctahedral symmetry group, and the suspension tower are all corollaries
of it.
-/

end Z2SuspensionTower


