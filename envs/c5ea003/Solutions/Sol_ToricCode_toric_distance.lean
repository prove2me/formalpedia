-- Prove2me | solution 1 for ToricCode.toric_distance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:53:10.674989+00:00
-- url     : https://prove2.me/submissions/ac07c48d-c5b2-4c72-a220-9f4551c17ae6

-- Sol generated from Geometry/ToricCode/Distance.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_M_le_weight_of_hWind
import Theorems.Thm_ToricCode_N_le_weight_of_vWind
import Theorems.Thm_ToricCode_hWind_loopH
import Theorems.Thm_ToricCode_hWind_of_boundary
import Theorems.Thm_ToricCode_hammingNorm_loopH
import Theorems.Thm_ToricCode_hammingNorm_loopV
import Theorems.Thm_ToricCode_loopH_cycle
import Theorems.Thm_ToricCode_loopV_cycle
import Theorems.Thm_ToricCode_vWind_loopV
import Theorems.Thm_ToricCode_winding_ne_zero_of_not_boundary
/-!
# The `Z`-distance of the `M × N` toric code is exactly `min M N`

This is the geometric heart of the development.  For the grid cellulation of the
torus `(ℤ/M) × (ℤ/N)` we prove

  `distance M N = min M N`,

i.e. the minimal Hamming weight of a cellular one-cycle that is not a boundary
is exactly the smaller of the two side lengths.  Together with
`ToricCode.toric_homologyRank` this establishes the parameters
`[[2MN, 2, min M N]]`, specialising to the classical `[[2L², 2, L]]` for the
square torus.

## Strategy

For each `i : ZMod M` the *column cut* consists of the `N` horizontal edges
`(false, (i, y))`.  The parity of a chain on this cut is `hWind z i`.  Dually
`vWind z j` is the parity on the *row cut* of vertical edges `(true, (x, j))`.

* `hWind_const` / `vWind_const`: for a cycle these parities do not depend on the
  cut.  (This is discrete Stokes: the difference of two neighbouring cut parities
  is the sum of the vertex boundary over a column.)
* `hWind_of_boundary` / `vWind_of_boundary`: they vanish on boundaries.
* `winding_ne_zero_of_not_boundary`: conversely, a cycle with both windings zero
  *is* a boundary.  This is proved by a dimension count: the winding map
  `cycles → 𝔽₂²` is onto, so its kernel has dimension `MN - 1`, which is exactly
  the dimension of the boundary space computed in `ToricCode.Homology`.
* Hence a logical operator has odd parity on each of the `M` pairwise disjoint
  column cuts, or on each of the `N` pairwise disjoint row cuts, so it uses at
  least `min M N` edges; and the two coordinate loops, of weights `M` and `N`,
  realise the bound.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-! ### Winding parities -/



/-- Reindexing a sum over `ZMod K` by a translation. -/
lemma sum_shift {K : ℕ} [NeZero K] (f : ZMod K → F2) (a : ZMod K) :
    ∑ y : ZMod K, f (y - a) = ∑ y : ZMod K, f y :=
  Equiv.sum_comp (Equiv.subRight a) f






/-! ### Windings vanish on boundaries -/


lemma vWind_of_boundary (g : Face M N → F2) (j : ZMod N) :
    vWind M N (d2 M N *ᵥ g) j = 0 := by
  have hexp : ∀ x : ZMod M, (d2 M N *ᵥ g) (true, (x, j)) = g (x, j) + g (x - 1, j) := by
    intro x
    rw [d2_mulVec]
    simp
  rw [vWind, Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_add_distrib]
  have hs : (∑ x : ZMod M, g (x - 1, j)) = ∑ x : ZMod M, g (x, j) :=
    sum_shift (fun x => g (x, j)) 1
  rw [hs]
  have h2 : ∀ x : F2, x + x = 0 := by decide
  exact h2 _

/-! ### The winding map and its surjectivity -/











lemma loopH_mem : loopH M N ∈ cycles M N := by
  simpa [cycles, LinearMap.mem_ker] using loopH_cycle M N

lemma loopV_mem : loopV M N ∈ cycles M N := by
  simpa [cycles, LinearMap.mem_ker] using loopV_cycle M N


/-! ### The kernel of the winding map is exactly the boundary space -/






/-! ### The distance -/






/-- **Lower bound.**  Every logical operator touches at least `min M N` edges. -/
theorem min_le_weight {z : Edge M N → F2} (hz : z ∈ cycles M N) (hnb : z ∉ boundaries M N) :
    min M N ≤ hammingNorm z := by
  rcases winding_ne_zero_of_not_boundary M N hz hnb with h | h
  · exact le_trans (min_le_left _ _) (M_le_weight_of_hWind M N hz h)
  · exact le_trans (min_le_right _ _) (N_le_weight_of_vWind M N hz h)

lemma loopH_not_boundary : loopH M N ∉ boundaries M N := by
  rintro ⟨g, hg⟩
  have h := hWind_of_boundary M N g 0
  rw [show (d2 M N) *ᵥ g = loopH M N from hg, hWind_loopH] at h
  exact one_ne_zero h

lemma loopV_not_boundary : loopV M N ∉ boundaries M N := by
  rintro ⟨g, hg⟩
  have h := vWind_of_boundary M N g 0
  rw [show (d2 M N) *ᵥ g = loopV M N from hg, vWind_loopV] at h
  exact one_ne_zero h







/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer).
  The previous cycle proved `distance = systole` abstractly and showed that the
  abstract homology rank cannot determine the distance.  The natural bold
  conjecture is that a genuine cellulation *does* determine it, and that the
  `M × N` torus grid realises exactly `[[2MN, 2, min M N]]`: a shortest
  noncontractible cellular loop should have to cross each of the `M` disjoint
  column cuts, or each of the `N` disjoint row cuts, an odd number of times.

Experiment (Experimenter).
  Before formalising, the square case was tested by exhaustive enumeration over
  all `2^(2L²)` binary one-chains, using the very definitions of this directory
  (`d1`, `d2`, `hammingNorm`).  Data (`min` = minimum weight of a cycle that is
  not a boundary):

    L = 1 :  #cycles =    4,  #boundaries =   1,  min = 1   (dual: min = 1)
    L = 2 :  #cycles =   32,  #boundaries =   8,  min = 2   (dual: min = 2)
    L = 3 :  #cycles = 1024,  #boundaries = 256,  min = 3   (dual: min = 3)

  These match the predicted `#cycles = 2^(L²+1)`, `#boundaries = 2^(L²-1)`,
  `min = L`, and the predicted equality of primal and dual spectra.  `L = 4`
  would require enumerating `2³²` chains and was not attempted; the general
  proof supersedes it.  The full logical weight spectra were also enumerated
  (`1,2` for `L=1`; `2,4,6` for `L=2`; `3,5,6,…,15,18` for `L=3`), refuting the
  stronger guess that all logical operators have weight `L`.

Analysis (Analyst).
  Two ingredients were needed and both survived formalisation.  (i) *Discrete
  Stokes*: summing the vertex boundary over a full column shows neighbouring cut
  parities agree, so a cycle has a well-defined pair of winding parities
  (`hWind_const`, `vWind_const`).  (ii) *A dimension count replaces an explicit
  potential function*: proving directly that a cycle with zero windings bounds
  would require constructing a face chain by integrating along paths on the
  torus, with awkward wrap-around cases.  Instead the winding map
  `cycles → 𝔽₂²` is shown to be onto, so its kernel has dimension `MN - 1`,
  which the independent computation `rank d₂ = MN - 1` identifies with the
  boundary space (`boundaries_eq_trivialWinding`).  The rank computation itself
  avoids bases entirely: `rank d₁ = rank d₁ᵀ` and the kernel of a coboundary is
  the line of constants, which is exactly connectivity of the torus graph and of
  its dual graph.  Crucially, *no step used `M = N`*: this is why the whole
  argument generalises to rectangular tori and yields `distance = min M N`.

Critique (Critic).
  Nothing here is vacuous: the lower bound `min M N ≤ hammingNorm z` genuinely
  uses the hypothesis `z ∉ boundaries`, and the value is attained, so
  `distance = min M N` is a two-sided statement.  The edge cases `M = 1` or
  `N = 1` are included and are not degenerate for the argument.  Nowhere is
  `decide` used on a statement depending on `M` or `N`; the only `decide` calls
  are on closed `𝔽₂` identities such as `1 + 1 = 0`.
-/
open ToricCode in
theorem solution: distance M N = min M N := by
  have hHmem : hammingNorm (loopH M N) ∈ logicalWeights M N :=
    ⟨loopH M N, loopH_mem M N, loopH_not_boundary M N, rfl⟩
  have hVmem : hammingNorm (loopV M N) ∈ logicalWeights M N :=
    ⟨loopV M N, loopV_mem M N, loopV_not_boundary M N, rfl⟩
  apply le_antisymm
  · apply le_min
    · have := Nat.sInf_le hHmem
      rwa [hammingNorm_loopH] at this
    · have := Nat.sInf_le hVmem
      rwa [hammingNorm_loopV] at this
  · apply le_csInf ⟨_, hHmem⟩
    rintro w ⟨z, hz, hnb, rfl⟩
    exact min_le_weight M N hz hnb
