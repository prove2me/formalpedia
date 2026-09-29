-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_GL3TropicalSatakeCore
-- name    : Bridges_TropicalAlgebra_GL3TropicalSatakeCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:12.263701+00:00
-- url     : https://prove2.me/theorems/23bcc9b7-f2ea-45ff-b5db-d83ee30c0e9f
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_GL3TropicalSatakeCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.GL3TropicalSatakeCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/GL3TropicalSatakeCore.lean by skeleton subtraction
import Mathlib

/-!
# Core objects of the GL₃ tropical Satake transform

This module supplies the definitions used by
`Bridges/TropicalAlgebra/TropicalSatakeSurjectivity.lean`, which referred to a
`GL3TropicalSatake` namespace that no module in the catalog provided.

The picture is the tropical (max-plus) shadow of the Satake isomorphism for `GL₃`:

* a *tropical Hecke function* is a symmetric function `ℤ³ → ℤ`, symmetry being encoded
  as invariance under sorting (`SortInvariant`, equivalent to `S₃`-invariance — the two
  transposition-invariances are derived in `sortInvariant_swap₁₂` and
  `sortInvariant_swap₂₃`);
* the *dominant chamber* `GL3Dom` is the subtype of weakly decreasing triples, an
  additive monoid;
* `satakeSupport` restricts a Hecke function to the dominant chamber and
  `satakeExtendHecke` extends a support datum back by sorting.

The two maps are mutually inverse; that is proved downstream.
-/

namespace GL3TropicalSatake

/-! ## Sorting a triple -/

/-- Sort a triple of integers into weakly decreasing order.  The middle entry is
recovered from the sum, which makes permutation invariance immediate. -/
def sort₃ (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (max a (max b c), a + b + c - max a (max b c) - min a (min b c), min a (min b c))

/-- The sorted triple is weakly decreasing. -/
theorem sort₃_dominant (a b c : ℤ) :
    (sort₃ a b c).2.1 ≤ (sort₃ a b c).1 ∧ (sort₃ a b c).2.2 ≤ (sort₃ a b c).2.1 := by
  simp only [sort₃, max_def, min_def]
  constructor <;> split_ifs <;> omega





/-! ## Tropical Hecke functions -/

/-- A function on `ℤ³` is *sort invariant* when it only depends on the sorted triple.
This is exactly `S₃`-invariance. -/
def SortInvariant (F : ℤ → ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c, F a b c = F (sort₃ a b c).1 (sort₃ a b c).2.1 (sort₃ a b c).2.2

/-- A tropical Hecke function for `GL₃`: a symmetric integer function on `ℤ³`. -/
def TropicalHeckeGL3 := {F : ℤ → ℤ → ℤ → ℤ // SortInvariant F}





/-! ## The dominant chamber -/

/-- The dominant chamber of `GL₃`: weakly decreasing integer triples. -/
def GL3Dom := {μ : ℤ × ℤ × ℤ // μ.2.1 ≤ μ.1 ∧ μ.2.2 ≤ μ.2.1}

instance : Zero GL3Dom := ⟨⟨(0, 0, 0), by constructor <;> simp⟩⟩

instance : Add GL3Dom :=
  ⟨fun x y => ⟨(x.1.1 + y.1.1, x.1.2.1 + y.1.2.1, x.1.2.2 + y.1.2.2), by
    obtain ⟨hx1, hx2⟩ := x.2
    obtain ⟨hy1, hy2⟩ := y.2
    exact ⟨add_le_add hx1 hy1, add_le_add hx2 hy2⟩⟩⟩

instance : DecidableEq GL3Dom := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- Sorting a triple into the dominant chamber. -/
def toGL3Dom (a b c : ℤ) : GL3Dom := ⟨sort₃ a b c, sort₃_dominant a b c⟩

/-! ## Support data and the Satake maps -/

/-- A *support datum*: an integer-valued function on the dominant chamber. -/
def SupportDatum := GL3Dom → ℤ

instance : Zero SupportDatum := ⟨fun _ => 0⟩



/-- Extension of a support datum to all of `ℤ³` by sorting. -/
def satakeExtend (h : SupportDatum) : ℤ → ℤ → ℤ → ℤ :=
  fun a b c => h (toGL3Dom a b c)



end GL3TropicalSatake


