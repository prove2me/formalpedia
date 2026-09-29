-- Prove2me | Definitions.Def_NumberTheory_MolienBurnsideElementaryAbelian
-- name    : NumberTheory_MolienBurnsideElementaryAbelian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:05.565979+00:00
-- url     : https://prove2.me/theorems/2966e9b2-d63d-41bb-ae8b-d8c6af8f53ea
-- title:
--   Aether Catalog definitions — NumberTheory_MolienBurnsideElementaryAbelian
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.MolienBurnsideElementaryAbelian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/MolienBurnsideElementaryAbelian.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10

/-!
# D10 fails for every elementary abelian group of rank two

The companion file `Catalog.NumberTheory.MolienBurnsideD10` refutes Conjecture D10 with a
`decide`-checked example over the Klein four group.  Here we upgrade that single example to
an **infinite family**, one for each prime `p`, with a genuine (non-`decide`) proof:

for `E = (ℤ/p)²` put

* `Xlines p = ⊔_{ℓ ∈ ℙ¹(𝔽_p)} E/ℓ`, the disjoint union of the `p+1` transitive `E`-sets of
  size `p` (indexed by the `p+1` lines through the origin, i.e. by the projective line),
* `Xreg p  = E ⊔ (p fixed points)`.

Both have `p(p+1) = p² + p` elements.  We show they have the *same permutation character*
(hence the same Molien invariant at every subgroup), while their Burnside marks at `⊤` are
`0` and `p` respectively; so no scaling relates the two mark vectors.

The heart of the computation is the projective-line count `card_vanishing_lines`: a nonzero
vector of `𝔽_p²` lies on exactly one of the `p+1` lines — an input from the theory of finite
fields (uniqueness of `-a/b`), which is what makes the character values agree.
-/

namespace D10

open Finset

section ElementaryAbelian

variable (p : ℕ) [Fact p.Prime]

/-- The elementary abelian group `(ℤ/p)²`, written multiplicatively. -/
abbrev EA (p : ℕ) := Multiplicative (ZMod p × ZMod p)

/-- The `p+1` characters of `(ℤ/p)²` with distinct kernels, indexed by the projective line
`ℙ¹(𝔽_p) = 𝔽_p ∪ {∞}`. -/
def eaChar (i : Option (ZMod p)) (v : ZMod p × ZMod p) : ZMod p :=
  match i with
  | some c => v.1 + c * v.2
  | none => v.2

@[simp] theorem eaChar_zero (i : Option (ZMod p)) : eaChar p i 0 = 0 := by
  cases i <;> simp [eaChar]

theorem eaChar_add (i : Option (ZMod p)) (u v : ZMod p × ZMod p) :
    eaChar p i (u + v) = eaChar p i u + eaChar p i v := by
  cases i with
  | none => simp [eaChar]
  | some c =>
      simp only [eaChar, Prod.fst_add, Prod.snd_add]
      ring


/-- The `E`-set `⊔_{ℓ} E/ℓ`: for each of the `p+1` lines a copy of `ℤ/p`, acted on through
the corresponding character. -/
abbrev Xlines (p : ℕ) := ZMod p × Option (ZMod p)

/-- The `E`-set `E ⊔ (p fixed points)`. -/
abbrev XregEA (p : ℕ) := (ZMod p × ZMod p) ⊕ ZMod p

instance : SMul (EA p) (Xlines p) :=
  ⟨fun g x => (x.1 + eaChar p x.2 (Multiplicative.toAdd g), x.2)⟩

theorem smul_Xlines (g : EA p) (x : Xlines p) :
    g • x = (x.1 + eaChar p x.2 (Multiplicative.toAdd g), x.2) := rfl

instance : MulAction (EA p) (Xlines p) where
  one_smul x := by
    rw [smul_Xlines]
    simp
  mul_smul g h x := by
    simp only [smul_Xlines]
    have : Multiplicative.toAdd (g * h)
        = Multiplicative.toAdd g + Multiplicative.toAdd h := rfl
    rw [this, eaChar_add]
    simp only [Prod.mk.injEq]
    exact ⟨by ring, trivial⟩

instance : SMul (EA p) (XregEA p) :=
  ⟨fun g x => match x with
    | .inl q => .inl (q + Multiplicative.toAdd g)
    | .inr c => .inr c⟩

theorem smul_XregEA_inl (g : EA p) (q : ZMod p × ZMod p) :
    g • (Sum.inl q : XregEA p) = Sum.inl (q + Multiplicative.toAdd g) := rfl

theorem smul_XregEA_inr (g : EA p) (c : ZMod p) :
    g • (Sum.inr c : XregEA p) = Sum.inr c := rfl

instance : MulAction (EA p) (XregEA p) where
  one_smul x := by
    cases x with
    | inl q => rw [smul_XregEA_inl]; simp
    | inr c => rw [smul_XregEA_inr]
  mul_smul g h x := by
    cases x with
    | inl q =>
        rw [smul_XregEA_inl, smul_XregEA_inl, smul_XregEA_inl]
        have : Multiplicative.toAdd (g * h)
            = Multiplicative.toAdd g + Multiplicative.toAdd h := rfl
        rw [this]
        congr 1
        abel
    | inr c => rw [smul_XregEA_inr, smul_XregEA_inr, smul_XregEA_inr]





instance decMemTopEA : DecidablePred (· ∈ (⊤ : Subgroup (EA p))) :=
  fun x => isTrue (Subgroup.mem_top x)




end ElementaryAbelian

end D10


