-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_TorusNerve
-- name    : MachineLearning_SheafCohomologyRobustness_TorusNerve
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T02:35:15.295757+00:00
-- url     : https://prove2.me/theorems/3e22ae83-cb31-4090-9e16-0be5afcf0fdd
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_TorusNerve
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.TorusNerve`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/TorusNerve.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_Cohomology
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# `H¹` of the Discrete Torus Nerve: Two Independent Adversarial Holonomies

A cover of a neural network's weight space by activation regions that is periodic
in **two** parameters (e.g. a two-parameter family of reparametrisations, or a
loop of layers crossed with a loop of input directions) has as nerve the discrete
torus: the `(m+1) × (n+1)` grid graph with wrap-around in both directions.

This file computes its first Čech cohomology exactly.  A `1`-cochain is a pair
`(h, v)` of horizontal and vertical overlap discrepancies; the Čech `2`-cocycle
condition (`Flat`) is the vanishing of the discrepancy around each unit
plaquette.  The results:

* `flat_of_coboundary` — coboundaries are flat (`δ² = 0` for the grid).
* `rowHol_const`, `colHol_const` — for a flat cochain the row holonomy is
  independent of the row and the column holonomy is independent of the column:
  the two holonomies are well-defined invariants.
* `torus_isCoboundary_iff` — a flat cochain is a coboundary **iff both**
  holonomies vanish.  The explicit potential `torusPotential` is built by
  integrating `h` along the base row and then `v` up each column, the
  plaquette condition being exactly what makes this consistent.
* `torusH1EquivProd`, `finrank_torusH1` — hence
  `H¹(torus nerve, ℝ) ≃ₗ[ℝ] ℝ × ℝ` and `dim H¹ = 2`.  A doubly periodic cover
  carries **two** independent adversarial obstruction classes, in exact analogy
  with the first Betti number of the topological torus.

This is a genuine cross-domain statement: a Künneth-type computation of a
discrete cohomology, applied to certified robustness bookkeeping.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer, bold): "the number of independent adversarial
  obstruction classes of a periodic cover equals the first Betti number of the
  nerve; for a doubly periodic cover it is `2`, not `1`."
* Experiment (Experimenter): the potential `P(a) + ∑_{b' < b} v(a, b')` fails
  the horizontal equation unless the plaquette identity is used to convert a
  telescoping sum of `v`-differences into a telescoping sum of `h`-differences;
  this conversion (`horizontal_transport`) is the technical heart, and it is
  where the `2`-cocycle condition earns its keep.
* Analysis (Analyst): the failed naive attempt (integrating `v` along the base
  column and `h` along rows) is not symmetric-equivalent — it needs the *same*
  plaquette identity in the transposed form.  Structural pattern: for a product
  nerve, the potential must be integrated in a fixed order, and flatness is the
  compatibility of the two orders.
* Critique (Critic): both holonomies are genuinely realised
  (`torus_holonomy_surjective` exhibits flat cochains with arbitrary prescribed
  holonomy pair), so `dim H¹ = 2` is not an artefact of a degenerate definition;
  and `finrank_torusH1` is proved from a constructed linear equivalence, not
  asserted.
* Synthesis (PI): together with `CyclicHolonomy` (`dim H¹ = 1` for the loop) this
  confirms the Betti-number reading of adversarial obstructions and gives the
  next conjecture: `dim H¹ = |E| - |V| + 1` for an arbitrary connected nerve.
-/


open BigOperators Finset

namespace SheafCohomologyRobustness
namespace TorusNerve

variable {m n : ℕ}

/-- Vertices of the discrete torus nerve: an `(m+1) × (n+1)` grid of cover
regions, periodic in both directions. -/
abbrev Grid (m n : ℕ) := Fin (m + 1) × Fin (n + 1)

/-- Horizontal component of the Čech coboundary of a `0`-cochain. -/
def dH (f : Grid m n → ℝ) : Grid m n → ℝ := fun p => f (p.1 + 1, p.2) - f p

/-- Vertical component of the Čech coboundary of a `0`-cochain. -/
def dV (f : Grid m n → ℝ) : Grid m n → ℝ := fun p => f (p.1, p.2 + 1) - f p

/-- **Plaquette (cocycle) condition.**  The total discrepancy around each unit
square of the nerve vanishes. -/
def Flat (h v : Grid m n → ℝ) : Prop :=
  ∀ p : Grid m n, h p + v (p.1 + 1, p.2) = v p + h (p.1, p.2 + 1)

/-- Holonomy around the horizontal loop at height `b`. -/
def rowHol (h : Grid m n → ℝ) (b : Fin (n + 1)) : ℝ := ∑ a, h (a, b)

/-- Holonomy around the vertical loop at abscissa `a`. -/
def colHol (v : Grid m n → ℝ) (a : Fin (m + 1)) : ℝ := ∑ b, v (a, b)

/-! ## §1. Elementary cyclic lemmas -/

/-- A function on a cyclic index set whose successive differences vanish is
constant. -/
lemma cyc_const_of_step {N : ℕ} {F : Fin (N + 1) → ℝ}
    (h : ∀ i : Fin (N + 1), F (i + 1) = F i) : ∀ i, F i = F 0 := by
  intro i
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => rfl
  | succ p ih =>
      have hp : p < N + 1 := by omega
      have hstep := h ⟨p, hp⟩
      have hfin : (⟨p, hp⟩ : Fin (N + 1)) + 1 = ⟨p + 1, hk⟩ := by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt hk]
      rw [hfin] at hstep
      rw [hstep]
      exact ih hp

/-- The discrete primitive of a difference telescopes, as long as the index does
not wrap around. -/
lemma partialSum_deltaCyc {N : ℕ} (w : Fin (N + 1) → ℝ) :
    ∀ (k : ℕ) (hk : k < N + 1), partialSum (deltaCyc w) k = w ⟨k, hk⟩ - w 0 := by
  intro k
  induction k with
  | zero => intro _; simp [partialSum]
  | succ p ih =>
      intro hk
      have hp : p < N + 1 := by omega
      rw [partialSum_succ _ p hp, ih hp]
      have hfin : (⟨p, hp⟩ : Fin (N + 1)) + 1 = ⟨p + 1, hk⟩ := by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt hk]
      simp only [deltaCyc, hfin]
      ring

lemma partialSum_sub {N : ℕ} (f g : Fin (N + 1) → ℝ) (k : ℕ) :
    partialSum (fun i => f i - g i) k = partialSum f k - partialSum g k := by
  simp [partialSum, Finset.sum_sub_distrib]

/-- Cyclic sums of successive differences vanish. -/
lemma sum_cyclic_diff {N : ℕ} (w : Fin (N + 1) → ℝ) :
    ∑ i : Fin (N + 1), (w (i + 1) - w i) = 0 := by
  rw [Finset.sum_sub_distrib]
  have : ∑ i : Fin (N + 1), w (i + 1) = ∑ i : Fin (N + 1), w i :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (N + 1))) w
  rw [this, sub_self]

/-! ## §2. Coboundaries are flat, and have vanishing holonomies -/

theorem flat_of_coboundary (f : Grid m n → ℝ) : Flat (dH f) (dV f) := by
  intro p
  simp only [dH, dV]
  ring

theorem rowHol_dH (f : Grid m n → ℝ) (b : Fin (n + 1)) : rowHol (dH f) b = 0 := by
  simp only [rowHol, dH]
  exact sum_cyclic_diff (fun a => f (a, b))

theorem colHol_dV (f : Grid m n → ℝ) (a : Fin (m + 1)) : colHol (dV f) a = 0 := by
  simp only [colHol, dV]
  exact sum_cyclic_diff (fun b => f (a, b))

/-! ## §3. The two holonomies of a flat cochain are well defined -/


theorem colHol_const {h v : Grid m n → ℝ} (hflat : Flat h v) (a : Fin (m + 1)) :
    colHol v a = colHol v 0 := by
  refine cyc_const_of_step (F := colHol v) ?_ a
  intro d
  have hstep : ∀ b : Fin (n + 1), v (d + 1, b) - v (d, b) = h (d, b + 1) - h (d, b) := by
    intro b
    have := hflat (d, b)
    simp only at this
    linarith
  have : colHol v (d + 1) - colHol v d = ∑ b : Fin (n + 1), (h (d, b + 1) - h (d, b)) := by
    simp only [colHol, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => hstep b
  rw [sum_cyclic_diff (fun b : Fin (n + 1) => h (d, b))] at this
  linarith

/-! ## §4. The explicit potential and the main computation -/

/-- The potential of a flat cochain with vanishing holonomies: integrate `h`
along the base row, then `v` up each column. -/
noncomputable def torusPotential (h v : Grid m n → ℝ) : Grid m n → ℝ :=
  fun p => partialSum (fun a => h (a, 0)) p.1.val + partialSum (fun b => v (p.1, b)) p.2.val

/-- Vertical equation for the potential (uses only the vanishing of the column
holonomies). -/
theorem dV_torusPotential {h v : Grid m n → ℝ} (hcol : ∀ a, colHol v a = 0) :
    dV (torusPotential h v) = v := by
  funext p
  simp only [dV, torusPotential]
  have hz : ∑ b, v (p.1, b) = 0 := hcol p.1
  have := congrFun (deltaCyc_of_sum_zero (fun b => v (p.1, b)) hz) p.2
  simp only [deltaCyc] at this
  linarith [this]

/-- Horizontal transport: the plaquette condition converts the difference of two
neighbouring column integrals into a telescoping sum of `h`-differences. -/
theorem horizontal_transport {h v : Grid m n → ℝ} (hflat : Flat h v)
    (a : Fin (m + 1)) (b : Fin (n + 1)) :
    partialSum (fun b' => v (a + 1, b')) b.val - partialSum (fun b' => v (a, b')) b.val
      = h (a, b) - h (a, 0) := by
  have hstep : (fun b' => v (a + 1, b') - v (a, b'))
      = deltaCyc (fun b' => h (a, b')) := by
    funext b'
    have := hflat (a, b')
    simp only [deltaCyc]
    simp only at this
    linarith
  rw [← partialSum_sub, hstep, partialSum_deltaCyc (fun b' => h (a, b')) b.val b.isLt]

/-- Horizontal equation for the potential (uses the base-row holonomy and
flatness). -/
theorem dH_torusPotential {h v : Grid m n → ℝ} (hflat : Flat h v)
    (hrow : rowHol h 0 = 0) : dH (torusPotential h v) = h := by
  funext p
  simp only [dH, torusPotential]
  have hz : ∑ a, h (a, 0) = 0 := hrow
  have hbase := congrFun (deltaCyc_of_sum_zero (fun a => h (a, 0)) hz) p.1
  simp only [deltaCyc] at hbase
  have htrans := horizontal_transport hflat p.1 p.2
  linarith [hbase, htrans]

/-- **Main theorem: the obstruction of the torus nerve is the pair of
holonomies.**  A flat overlap discrepancy on the doubly periodic cover glues to a
global potential if and only if both loop holonomies vanish. -/
theorem torus_isCoboundary_iff {h v : Grid m n → ℝ} (hflat : Flat h v) :
    (∃ f, dH f = h ∧ dV f = v) ↔ (rowHol h 0 = 0 ∧ colHol v 0 = 0) := by
  constructor
  · rintro ⟨f, rfl, rfl⟩
    exact ⟨rowHol_dH f 0, colHol_dV f 0⟩
  · rintro ⟨hrow, hcol⟩
    have hcolall : ∀ a, colHol v a = 0 := fun a => by rw [colHol_const hflat a, hcol]
    exact ⟨torusPotential h v, dH_torusPotential hflat hrow, dV_torusPotential hcolall⟩

/-- Both holonomies are realised: for any prescribed pair `(r, c)` there is a
flat cochain with those holonomies (take the constant cochains). -/
theorem torus_holonomy_surjective (m n : ℕ) (r c : ℝ) :
    ∃ h v : Grid m n → ℝ, Flat h v ∧ rowHol h 0 = r ∧ colHol v 0 = c := by
  refine ⟨fun _ => r / (m + 1), fun _ => c / (n + 1), fun p => by ring, ?_, ?_⟩
  · have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    simp only [rowHol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [colHol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-! ## §5. `H¹(torus) ≃ ℝ²` -/

/-- The space of flat (cocycle) `1`-cochains on the torus nerve. -/
def flatSubmodule (m n : ℕ) : Submodule ℝ ((Grid m n → ℝ) × (Grid m n → ℝ)) where
  carrier := {z | Flat z.1 z.2}
  add_mem' := by
    intro z w hz hw p
    have h1 := hz p
    have h2 := hw p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    linarith
  zero_mem' := by intro p; simp
  smul_mem' := by
    intro a z hz p
    have h1 := hz p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    linear_combination a * h1

/-- The Čech coboundary as a linear map into pairs of overlap discrepancies. -/
def deltaPair (m n : ℕ) :
    (Grid m n → ℝ) →ₗ[ℝ] ((Grid m n → ℝ) × (Grid m n → ℝ)) where
  toFun f := (dH f, dV f)
  map_add' f g := by
    apply Prod.ext <;> funext p <;>
      simp only [dH, dV, Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a f := by
    apply Prod.ext <;> funext p <;>
      simp only [dH, dV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst,
        Prod.smul_snd] <;> ring

/-- The Čech coboundary as a linear map into the flat cochains. -/
def deltaT (m n : ℕ) : (Grid m n → ℝ) →ₗ[ℝ] flatSubmodule m n :=
  (deltaPair m n).codRestrict (flatSubmodule m n) (fun f => flat_of_coboundary f)

/-- The pair of holonomies as a linear functional on flat cochains. -/
def holT (m n : ℕ) : flatSubmodule m n →ₗ[ℝ] ℝ × ℝ where
  toFun z := (rowHol z.1.1 0, colHol z.1.2 0)
  map_add' z w := by
    apply Prod.ext <;>
      simp [rowHol, colHol, Finset.sum_add_distrib]
  map_smul' a z := by
    apply Prod.ext <;>
      simp [rowHol, colHol, Finset.mul_sum]

theorem range_deltaT_eq_ker_holT (m n : ℕ) :
    LinearMap.range (deltaT m n) = LinearMap.ker (holT m n) := by
  ext z
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨f, hf⟩
    have h1 : dH f = z.1.1 := by rw [← hf]; rfl
    have h2 : dV f = z.1.2 := by rw [← hf]; rfl
    have : (rowHol z.1.1 0, colHol z.1.2 0) = ((0 : ℝ), (0 : ℝ)) := by
      rw [← h1, ← h2, rowHol_dH, colHol_dV]
    simpa [holT] using this
  · intro hz
    have hz' : rowHol z.1.1 0 = 0 ∧ colHol z.1.2 0 = 0 := by
      have := congrArg Prod.fst hz
      have h2 := congrArg Prod.snd hz
      exact ⟨by simpa [holT] using this, by simpa [holT] using h2⟩
    obtain ⟨f, hf1, hf2⟩ := (torus_isCoboundary_iff z.2).mpr hz'
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact Prod.ext hf1 hf2

theorem holT_surjective (m n : ℕ) : Function.Surjective (holT m n) := by
  rintro ⟨r, c⟩
  obtain ⟨h, v, hflat, hr, hc⟩ := torus_holonomy_surjective m n r c
  exact ⟨⟨(h, v), hflat⟩, by simp [holT, hr, hc]⟩

/-- **`H¹` of the discrete torus nerve is `ℝ²`.**  The two loop holonomies form a
complete set of invariants of a flat overlap discrepancy modulo coboundaries. -/
noncomputable def torusH1EquivProd (m n : ℕ) :
    (flatSubmodule m n ⧸ LinearMap.range (deltaT m n)) ≃ₗ[ℝ] ℝ × ℝ :=
  (Submodule.quotEquivOfEq _ _ (range_deltaT_eq_ker_holT m n)).trans
    ((holT m n).quotKerEquivOfSurjective (holT_surjective m n))



end TorusNerve
end SheafCohomologyRobustness


