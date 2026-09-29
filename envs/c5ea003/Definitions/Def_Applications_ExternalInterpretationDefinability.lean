-- Prove2me | Definitions.Def_Applications_ExternalInterpretationDefinability
-- name    : Applications_ExternalInterpretationDefinability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:05.440124+00:00
-- url     : https://prove2.me/theorems/19e57203-5562-4cc3-84c3-dc2386ae4496
-- title:
--   Aether Catalog definitions — Applications_ExternalInterpretationDefinability
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ExternalInterpretationDefinability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ExternalInterpretationDefinability.lean by skeleton subtraction
import Mathlib
/-
# The Definability Boundary for External Interpretations

An **external interpretation** of a structure `M` is a map `I : M → V` assigning
to each element of the structure a "meaning" drawn from an outside value type `V`.
The structure itself only sees its elements up to its symmetries: two elements
lying in the same orbit of the automorphism group `G` are *structurally
indistinguishable*.  The guiding question of this file is:

> When is an external interpretation *recoverable from structural truth*, i.e.
> when does it factor through the structural quotient, and when is it moreover
> *definable* in a language of invariant predicates?

The conjecture under test is:

> recoverable ⟺ constant on automorphism orbits **and** definable in the
> invariant language; for finite models orbit constancy alone suffices once the
> language is enriched by (bounded) orbit-counting modalities.

What we prove:

* **Part 1 — Orbit descent.**  `recoverable_iff_orbitConstant` : an
  interpretation factors through the orbit quotient exactly when it is constant
  on orbits, and `recovery_unique` shows the factorisation is unique.  This is
  the "necessary condition" half of the conjecture, proved in full generality.
* **Part 2 — Meaning collision.**  `not_recoverable_of_collision` and
  `perm_recoverable_iff_constant` : under the full symmetric group every
  non-constant interpretation collides, so structural truth cannot recover it;
  `meaning_collision_bool` is a concrete two-element instance.  This is the
  negative half of the classification.
* **Part 3 — Invariant languages.**  Definability in *any* invariant language
  implies orbit constancy (`definable_orbitConstant`), hence recoverability
  (`definable_recoverable`): definability is genuinely the stronger notion.
* **Part 4 — Finite sufficiency.**  For a finite model, every invariant set is
  a Boolean combination of orbit predicates (`countGen_of_invariantSet`), and
  conversely (`invariantSet_of_countGen`).  Consequently
  `finite_recoverable_iff_definable` : on finite models the three notions
  (recoverable, orbit-constant, definable in the counting language) coincide —
  the conjectured collapse in the finite case, and `orbitLang` is shown to be
  the largest invariant language (`orbitLang_maximal`).  In general (no
  finiteness) `definable_orbitLang_iff_recoverable` shows recoverability is
  exactly definability in that largest invariant language, and
  `classification_finite` packages the finite collapse as a `TFAE`.
* **Part 5 — The infinite boundary is real.**  `parity_not_definable` exhibits
  an interpretation on `ℕ` which is orbit-constant (indeed the group is trivial)
  yet undefinable in the finite/cofinite invariant language: orbit constancy
  alone is *strictly weaker* than definability, so the definability clause in
  the conjecture cannot be dropped for infinite models.
* **Part 6 — A Burnside bridge.**  `card_orbitConstant_eq_pow` counts the
  recoverable interpretations as `|V| ^ (number of orbits)`, and
  `burnside_recoverable_count` combines this with the orbit-counting lemma:
  `2 ^ (∑_g |Fix g|) = (number of recoverable Boolean interpretations) ^ |G|`,
  linking semantic recoverability to group-theoretic character sums.
-/


namespace ExternalInterpretationDefinability

open MulAction

universe u v w

variable {G : Type u} {M : Type v} {V : Type w} [Group G] [MulAction G M]

/-! ## Part 0 — Structural indistinguishability -/

/-- Two elements are **structurally indistinguishable** when some automorphism
(element of the acting group `G`) carries one to the other. -/
def Indist (G : Type u) [Group G] [MulAction G M] (x y : M) : Prop := ∃ g : G, g • x = y


lemma indist_symm {x y : M} (h : Indist G x y) : Indist G y x := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, by simp⟩


/-- Indistinguishability is exactly the Mathlib orbit relation (with arguments
swapped, matching `MulAction.orbitRel_apply`). -/
lemma indist_iff_orbitRel {x y : M} : Indist G x y ↔ (orbitRel G M) y x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact Iff.rfl

/-- An interpretation is **orbit-constant** if indistinguishable elements get the
same meaning. -/
def OrbitConstant (G : Type u) [Group G] [MulAction G M] (I : M → V) : Prop :=
  ∀ ⦃x y : M⦄, Indist G x y → I x = I y

/-- An interpretation is **recoverable from structural truth** if it factors
through the quotient of the model by structural indistinguishability. -/
def Recoverable (G : Type u) [Group G] [MulAction G M] (I : M → V) : Prop :=
  ∃ F : orbitRel.Quotient G M → V, ∀ x : M, F (Quotient.mk _ x) = I x

/-! ## Part 1 — Orbit descent -/



/-! ## Part 2 — Meaning collisions: the negative half -/




/-! ## Part 3 — Invariant languages and definability -/

/-- A set is **invariant** if it is closed under the action of the group. -/
def InvariantSet (G : Type u) [Group G] [MulAction G M] (s : Set M) : Prop :=
  ∀ (g : G) ⦃x : M⦄, x ∈ s → g • x ∈ s

/-- An **invariant language** on `M`: a Boolean algebra of subsets of `M`, all of
whose members are invariant under the automorphism group. -/
structure InvLang (G : Type u) (M : Type v) [Group G] [MulAction G M] where
  /-- The sets definable by a formula of the language. -/
  Defble : Set M → Prop
  /-- The empty set is definable (by a contradictory formula). -/
  empty_mem : Defble ∅
  /-- Definable sets are closed under negation. -/
  compl_mem : ∀ {s : Set M}, Defble s → Defble sᶜ
  /-- Definable sets are closed under disjunction. -/
  union_mem : ∀ {s t : Set M}, Defble s → Defble t → Defble (s ∪ t)
  /-- Every definable set is invariant: the language sees only structure. -/
  invariant : ∀ {s : Set M}, Defble s → InvariantSet G s

/-- An interpretation is **definable** in an invariant language when each of its
meaning fibres is definable. -/
def Definable (L : InvLang G M) (I : M → V) : Prop := ∀ v : V, L.Defble {x | I x = v}




/-! ## Part 4 — Orbit predicates, counting modalities, and finite sufficiency -/


lemma invariantSet_empty : InvariantSet G (∅ : Set M) := by
  intro g x hx; exact absurd hx (Set.notMem_empty x)

lemma invariantSet_compl {s : Set M} (hs : InvariantSet G s) : InvariantSet G sᶜ := by
  intro g x hx hmem
  exact hx (by simpa using hs g⁻¹ hmem)

lemma invariantSet_union {s t : Set M} (hs : InvariantSet G s) (ht : InvariantSet G t) :
    InvariantSet G (s ∪ t) := by
  rintro g x (hx | hx)
  · exact Or.inl (hs g hx)
  · exact Or.inr (ht g hx)


/-- The **orbit language**: all invariant subsets of `M`.  It is an invariant
language, and by `orbitLang_maximal` the largest one. -/
def orbitLang (G : Type u) (M : Type v) [Group G] [MulAction G M] : InvLang G M where
  Defble := InvariantSet G
  empty_mem := invariantSet_empty
  compl_mem := invariantSet_compl
  union_mem := invariantSet_union
  invariant := id


/-- Sets definable by a Boolean combination of **orbit (counting) modalities**:
the smallest Boolean algebra of subsets containing every orbit. -/
inductive CountGen (G : Type u) (M : Type v) [Group G] [MulAction G M] : Set M → Prop
  | orbit (x : M) : CountGen G M (MulAction.orbit G x)
  | empty : CountGen G M ∅
  | compl {s : Set M} : CountGen G M s → CountGen G M sᶜ
  | union {s t : Set M} : CountGen G M s → CountGen G M t → CountGen G M (s ∪ t)










/-! ## Part 5 — The infinite boundary: orbit constancy is strictly weaker -/

section InfiniteBoundary

/-- The trivial automorphism group of `ℕ`: the bottom subgroup of `Equiv.Perm ℕ`. -/
abbrev TrivG : Type := (⊥ : Subgroup (Equiv.Perm ℕ))

lemma trivG_smul (g : TrivG) (n : ℕ) : g • n = n := by
  obtain ⟨g, hg⟩ := g
  rw [Subgroup.mem_bot] at hg
  subst hg
  rfl


/-- The invariant language of finite-or-cofinite subsets of `ℕ` (the "bounded"
language: a formula may only pin down finitely much information, or its
negation may). -/
def cofiniteLang : InvLang TrivG ℕ where
  Defble s := s.Finite ∨ sᶜ.Finite
  empty_mem := Or.inl Set.finite_empty
  compl_mem := by
    rintro s (h | h)
    · exact Or.inr (by simpa using h)
    · exact Or.inl h
  union_mem := by
    rintro s t (hs | hs) (ht | ht)
    · exact Or.inl (hs.union ht)
    · refine Or.inr (Set.Finite.subset ht ?_)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx ⊢
      exact hx.2
    · refine Or.inr (Set.Finite.subset hs ?_)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx ⊢
      exact hx.1
    · refine Or.inr (Set.Finite.subset hs ?_)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx ⊢
      exact hx.1
  invariant := by
    intro s _ g x hx
    rw [trivG_smul]
    exact hx

/-- The parity interpretation of `ℕ`. -/
def parity : ℕ → Bool := fun n => decide (Even n)






end InfiniteBoundary

/-! ## Part 6 — Counting the recoverable interpretations (Burnside bridge) -/

/-- Recoverable interpretations correspond bijectively to functions on the orbit
space. -/
def recoverableEquiv (G : Type u) (M : Type v) (V : Type w) [Group G] [MulAction G M] :
    {I : M → V // OrbitConstant G I} ≃ (orbitRel.Quotient G M → V) where
  toFun I := Quotient.lift I.1 (by
    intro a b hab
    have hr : (orbitRel G M) a b := hab
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
    exact (I.2 hr).symm)
  invFun F := ⟨fun x => F (Quotient.mk _ x), by
    intro x y hxy
    have : (Quotient.mk (orbitRel G M) x) = Quotient.mk _ y :=
      Quotient.sound (indist_iff_orbitRel.mp (indist_symm hxy))
    simp only
    rw [this]⟩
  left_inv := by rintro ⟨I, hI⟩; rfl
  right_inv := by
    intro F
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl



end ExternalInterpretationDefinability


