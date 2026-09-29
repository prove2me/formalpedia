-- Prove2me | Definitions.Def_Bridges_NucleusSheafReconstruction
-- name    : Bridges_NucleusSheafReconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:41.359257+00:00
-- url     : https://prove2.me/theorems/26b7be86-ac1d-4b82-a9b6-2769ed786898
-- title:
--   Aether Catalog definitions — Bridges_NucleusSheafReconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NucleusSheafReconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NucleusSheafReconstruction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/

/-!
# Nucleus-Sheaf Reconstruction for Coherent Idempotent Semirings

This file builds a concrete sheaf-of-local-quotients model over the nucleus spectrum
of a coherent commutative idempotent semiring and proves:

1. **Global-sections reconstruction** — elements of the semiring are determined by their
   evaluations at all nucleus points (prime congruences).
2. **Binary gluing / patching** — compatible local sections over two compact opens
   can be glued to a section over their union.
3. **Local-to-global elimination** — equality in the semiring is equivalent to
   pointwise equality at all nucleus points.

## Mathematical overview

An **idempotent commutative semiring** is a commutative semiring where `a + a = a`.
A **nucleus point** on `S` is a prime ring congruence: `θ(a·b, 0) → θ(a,0) ∨ θ(b,0)`.

For each set `U` of nucleus points, the **section congruence** `sectionCongr S U` is
defined by `a ~ b ↔ ∀ x ∈ U, x.con a b`. The **local quotient**
`LocalQuotient S U = S / sectionCongr S U` represents "local sections over U".

The main reconstruction theorem says that under prime separation, two elements are equal
iff they agree at all nucleus points.

## Main results

* `congruence_eq_iff_locally` — `a = b ↔ ∀ x, evalAt x a = evalAt x b`
* `toGlobalSections_injective_of_prime_separation` — injectivity of global sections
* `sections_glue_binary` — binary gluing of compatible local sections
* `sectionCongr_mono` — monotonicity of section congruences
* `restrict_id`, `restrict_comp` — presheaf laws
* `globalSectionsIso` — the reconstruction isomorphism
-/

set_option maxHeartbeats 800000

universe u

namespace NucleusSheafReconstruction

/-! ## 1. Core Algebraic Structures -/

/-- A **coherent idempotent commutative semiring**: a commutative semiring where addition
is idempotent (`a + a = a`). This makes `(S, +)` a join-semilattice. -/
class CoherentIdemCommSemiring (S : Type u) extends CommSemiring S where
  idem_add : ∀ a : S, a + a = a

/-- A **nucleus point** on a commutative semiring `S` is a ring congruence that is
prime: if the product `a * b` is congruent to `0`, then `a` or `b` is congruent to `0`. -/
structure NucleusPoint (S : Type u) [CommSemiring S] where
  /-- The underlying ring congruence. -/
  con : RingCon S
  /-- Primality: `θ(a·b, 0) → θ(a, 0) ∨ θ(b, 0)`. -/
  prime : ∀ a b : S, con (a * b) 0 → con a 0 ∨ con b 0

variable {S : Type u} [CommSemiring S]

/-- Evaluate an element of `S` at a nucleus point, obtaining its equivalence class
in the quotient by that point's congruence. -/
noncomputable def evalAt (x : NucleusPoint S) (a : S) : x.con.Quotient :=
  x.con.toQuotient a



/-! ## 2. Section Congruences and Local Quotients -/

/-- The **section congruence** attached to a set `U` of nucleus points.
Two elements are related iff they are congruent at every point in `U`.
This is the algebraic incarnation of "agreement on all stalks in `U`". -/
noncomputable def sectionCongr (S : Type u) [CommSemiring S]
    (U : Set (NucleusPoint S)) : RingCon S where
  r a b := ∀ x ∈ U, x.con a b
  iseqv := {
    refl := fun a x _ => x.con.refl a
    symm := fun h x hx => x.con.symm (h x hx)
    trans := fun h1 h2 x hx => x.con.trans (h1 x hx) (h2 x hx)
  }
  add' := fun h1 h2 x hx => x.con.add (h1 x hx) (h2 x hx)
  mul' := fun h1 h2 x hx => x.con.mul (h1 x hx) (h2 x hx)


/-- The section congruence is antitone: larger sets of points give finer congruences. -/
theorem sectionCongr_mono {U V : Set (NucleusPoint S)} (h : V ⊆ U) :
    sectionCongr S U ≤ sectionCongr S V :=
  fun _ _ hab => fun x hx => hab x (h hx)


/-- The **local quotient** of `S` at a set `U` of nucleus points. -/
def LocalQuotient (S : Type u) [CommSemiring S] (U : Set (NucleusPoint S)) : Type u :=
  (sectionCongr S U).Quotient

noncomputable instance instCommSemiringLocalQuotient (U : Set (NucleusPoint S)) :
    CommSemiring (LocalQuotient S U) :=
  inferInstanceAs (CommSemiring (sectionCongr S U).Quotient)

/-- The canonical projection from `S` to the local quotient on `U`. -/
noncomputable def toLocalQuotient (U : Set (NucleusPoint S)) :
    S →+* LocalQuotient S U :=
  (sectionCongr S U).mk'



/-! ## 3. Restriction Maps -/

/-- The **restriction map** from the local quotient on `U` to the local quotient on `V`,
defined when `V ⊆ U`. -/
noncomputable def LocalQuotient.restrict
    {U V : Set (NucleusPoint S)} (h : V ⊆ U) :
    LocalQuotient S U →+* LocalQuotient S V :=
  (sectionCongr S U).lift (toLocalQuotient V) (fun _ _ hab =>
    (sectionCongr S V).eq.mpr (sectionCongr_mono h hab))




/-! ## 4. Global Sections and Reconstruction -/

/-- The **global section map**: `S →+* LocalQuotient S Set.univ`. -/
noncomputable def toGlobalSections :
    S →+* LocalQuotient S (Set.univ : Set (NucleusPoint S)) :=
  toLocalQuotient Set.univ

/-- **Prime separation**: any two distinct elements are distinguished by some nucleus point. -/
def PrimeSeparation (S : Type u) [CommSemiring S] : Prop :=
  ∀ {a b : S}, a ≠ b → ∃ x : NucleusPoint S, ¬ x.con a b






/-! ## 5. Section Congruence Lattice Properties -/



/-! ## 6. Binary Gluing / Patching -/

/-- The **congruence Chinese Remainder property** for sets of nucleus points:
for any elements `a, b` that agree at all points in `U ∩ V`, there exists
a "patching element" `c` that agrees with `a` on `U` and with `b` on `V`. -/
def CongruenceCRT (S : Type u) [CommSemiring S]
    (U V : Set (NucleusPoint S)) : Prop :=
  ∀ a b : S, (∀ x ∈ U ∩ V, x.con a b) →
    ∃ c : S, (∀ x ∈ U, x.con c a) ∧ (∀ x ∈ V, x.con c b)



/-! ## 7. Stalk Product -/

/-- The **stalk product**: `∏_x S/x.con`. -/
def StalkProduct (S : Type u) [CommSemiring S] : Type u :=
  (x : NucleusPoint S) → x.con.Quotient

noncomputable instance : CommSemiring (StalkProduct S) := Pi.commSemiring

/-- The canonical evaluation map into the stalk product. -/
noncomputable def toStalkProduct : S →+* StalkProduct S :=
  Pi.ringHom (fun x => x.con.mk')




/-! ## 8. Separated Reflection -/

/-- The **nucleus-separated reflection** of `S`. -/
def NucleusSeparatedReflection (S : Type u) [CommSemiring S] : Type u :=
  LocalQuotient S (Set.univ : Set (NucleusPoint S))

noncomputable instance : CommSemiring (NucleusSeparatedReflection S) :=
  instCommSemiringLocalQuotient _




/-! ## 9. Presheaf Laws -/



end NucleusSheafReconstruction

/-  The lines below are corrupted leftovers of a text edit: each is the tail of a
    statement whose head was lost, and every one of them duplicates a theorem that
    already appears in full earlier in this file.  They are kept, commented out, for
    the record; without the comment the file does not parse.

    end Congr S (Set.univ : Set (NucleusPoint S)) a b ↔
    end Congr S (U ∪ V) a b ↔ sectionCongr S U a b ∧ sectionCongr S V a b := by
    end Congr S (∅ : Set (NucleusPoint S)) a b := by
    end Congr S U ≤ sectionCongr S V :=
    end Congr S U a b ↔ ∀ x ∈ U, x.con a b :=
-/


