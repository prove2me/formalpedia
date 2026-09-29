-- Prove2me | Definitions.Def_Bridges_RamseyTheory_ChromaticDarkness
-- name    : Bridges_RamseyTheory_ChromaticDarkness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:24.808976+00:00
-- url     : https://prove2.me/theorems/6b4039de-b208-4606-8c1b-c0ae558564da
-- title:
--   Aether Catalog definitions — Bridges_RamseyTheory_ChromaticDarkness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.RamseyTheory.ChromaticDarkness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/RamseyTheory/ChromaticDarkness.lean by skeleton subtraction
import Mathlib

/-!
# Chromatic Darkness: Partition Duality and Extremal Structure

We develop the **chromatic theory of dark witness families** — a framework connecting
dark witness families to partition structures through "rejection sets."

## Key Insight

Every dark witness family has a **dual rejection perspective**: the rejection sets
must cover all candidates, and the *balance* of this covering determines extremal behavior.

## Novel Definitions

* `DarkFamily` — Dark witness family over `Fin m` worlds with candidates from `Fin N`.
* `rejection` — Rejection set of a world: candidates it does NOT accept.
* `spectrum` / `antiSpectrum` — Worlds accepting/rejecting each candidate.
* `defect` — Number of worlds rejecting each candidate (≥ 1 always).
* `IsBalanced` — Every candidate rejected by exactly one world.

## Main Results

* `rejection_covers` — Rejection sets cover all candidates.
* `spectrum_plus_defect` — Spectrum and defect are complementary.
* `double_count_identity` — Duality identity.
* `total_rejection_ge_N` — Total rejection ≥ N.
* `balanced_iff_partition` — Balanced families ↔ partition structure.
* `balanced_total_rejection` — Balanced families have total defect = N.
* `darkness_level_bound` — Level × m ≤ N × (m - 1).
* `witness_intersection_bound` — Overlap bound for balanced equitable families.
-/

namespace ChromaticDarkness

open Finset Fintype

/-! ### Core Structure -/

/-- A `DarkFamily m N` is a dark witness family with `m` worlds and candidates from `Fin N`. -/
structure DarkFamily (m N : ℕ) where
  witnesses : Fin m → Finset (Fin N)
  level : ℕ
  level_pos : 0 < level
  has_enough : ∀ a : Fin m, level ≤ (witnesses a).card
  no_universal : ∀ n : Fin N, ∃ a : Fin m, n ∉ witnesses a

variable {m N : ℕ}

/-! ### Rejection Perspective -/

/-- The **rejection set** of world `a`: candidates that world `a` does NOT accept. -/
def rejection (D : DarkFamily m N) (a : Fin m) : Finset (Fin N) :=
  Finset.univ \ D.witnesses a

/-- The **spectrum** of candidate `n`: worlds that accept `n` as a witness. -/
def spectrum (D : DarkFamily m N) (n : Fin N) : Finset (Fin m) :=
  Finset.univ.filter (fun a => n ∈ D.witnesses a)

/-- The **anti-spectrum** of candidate `n`: worlds that reject `n`. -/
def antiSpectrum (D : DarkFamily m N) (n : Fin N) : Finset (Fin m) :=
  Finset.univ.filter (fun a => n ∉ D.witnesses a)

/-- The **defect** of candidate `n`: the number of worlds that reject it. -/
def defect (D : DarkFamily m N) (n : Fin N) : ℕ :=
  (antiSpectrum D n).card

/-! ### Basic Lemmas -/




/-! ### Theorem 1: Rejection Cover -/


/-! ### Theorem 2: Spectrum-Defect Complement -/


/-
Spectrum size and defect sum to the total number of worlds.
-/


/-
Each candidate's spectrum is strictly smaller than the total number of worlds.
-/

/-! ### Rejection Size -/



/-! ### Theorem 3: Double Counting Identity -/

/-
**Double Counting Identity**: Total rejections by world = total defects by candidate.

Both sides count the same set of (world, candidate) pairs where the world rejects
the candidate. This is the fundamental duality of chromatic darkness theory.
-/

/-! ### Theorem 4: Total Rejection Bound -/

/-
**Total Rejection Lower Bound**: The sum of all defects is at least N.
Since every candidate must be rejected by at least one world, total rejections ≥ N.
-/

/-! ### Balanced Dark Families -/

/-- A dark family is **balanced** if every candidate is rejected by exactly one world. -/
def IsBalanced (D : DarkFamily m N) : Prop :=
  ∀ n : Fin N, defect D n = 1

/-
In a balanced family, spectrum size is exactly m - 1.
-/

/-! ### Theorem 5: Balanced Partition -/

/-
Balanced dark families' rejection sets form a partition: each candidate belongs
to exactly one rejection set.
-/

/-
In a balanced family, rejection sets are pairwise disjoint.
-/

/-! ### Theorem 6: Balanced Total Rejection -/

/-
Total defect in a balanced family is exactly N.
-/

/-! ### Theorem 7: Darkness Level Bound -/

/-
**Darkness Level Bound (Dark Inequality)**: level × m ≤ N × (m - 1).

The proof uses double counting: total rejections ≥ N (covering) and each world
has at most N - level rejections, so total ≤ m × (N - level). Combining:
N ≤ m × (N - level) = mN - m·level, hence m·level ≤ mN - N = N(m-1).
-/

/-! ### Chromatic Equivalence -/

/-- Two candidates are **chromatically equivalent** if they share the same rejection pattern. -/
def chromaticallyEquivalent (D : DarkFamily m N) (n₁ n₂ : Fin N) : Prop :=
  antiSpectrum D n₁ = antiSpectrum D n₂


/-! ### Theorem 8: Witness Intersection Bound -/

/-
For balanced equitable families, any two distinct worlds share at least
N - 2·(N/m) witnesses. Each world rejects N/m candidates, so two worlds
together reject at most 2·(N/m) candidates (by disjointness), leaving
at least N - 2·(N/m) common witnesses.
-/

end ChromaticDarkness


